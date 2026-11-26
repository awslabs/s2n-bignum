(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing with 13 bits per coefficient: the proof.                          *)
(*                                                                           *)
(* The code is clang 23's: one loop of 32 iterations, each loading eight    *)
(* coefficients with four LDP and storing 13 single bytes, then a stack      *)
(* guard check. The loop counter X10 counts down from 32.                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The 13 bytes written by an iteration, with the spec function unfolded:    *)
(* SIMP_TAC[DIVMOD_CHUNK; ARITH] on the chain of conditionals of             *)
(* mld_polyt0_pack takes seconds for each byte, so the byte 13 * i + k of    *)
(* the spec is first expressed as byte k of the spec of the coefficients     *)
(* from 8 * i, and then unfolded at a numeral k.                             *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYT0_PACK_SHIFT = prove
 (`!(x:num->int32) i k. k < 13
        ==> mld_polyt0_pack x (13 * i + k) =
            mld_polyt0_pack (\m. x (8 * i + m)) k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyt0_pack] THEN
  ASM_SIMP_TAC[DIVMOD_CHUNK; DIV_LT; MOD_LT] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The second word of an LDP at X9 + 0 or X9 + 8 is read at the address      *)
(* (a + 32 * i) + 20 or + 28, which ARM_STEPS_TAC does not identify with     *)
(* the address a + (32 * i + 20) of the input assumptions. LDP_FIX restates  *)
(* the assumptions at those addresses; otherwise the loaded register value   *)
(* is discarded as depending on an old state.                                *)
(* ------------------------------------------------------------------------- *)

let LDP_FIX = prove
 (`!(a:int64) i k s.
     read (memory :> bytes32 (word_add (word_add a (word (32 * i))) (word k))) s =
     read (memory :> bytes32 (word_add a (word (32 * i + k)))) s`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(*** The loop test: X10 counts down from 32 ***)

let T0_TEST = prove
 (`!i. i < 32
       ==> (val (word_sub (word_sub (word 32:int64) (word i)) (word 1)) = 0 <=>
            ~(i + 1 < 32))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let T0_FULL_FINAL_TAC (x:term) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MP (SPEC `i:num` T0_TEST) (ASSUME `i < 32`)] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      SIMP_TAC[MLD_POLYT0_PACK_SHIFT; ARITH] THEN
      REWRITE_TAC[mld_polyt0_pack] THEN
      CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 32 iterations   *)
(* of the loop handles one group of coefficients and its bytes. The loop     *)
(* test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires,    *)
(* and the events of an iteration depend on its index only.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (guard:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop r a guard pc stackpointer returnaddress i))
          (f_ev_prol r a guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mldsa_polyt0_pack_loop1`
   `pc + mldsa_polyt0_pack_loop1_exit`
   `\i s. read X8 s = word_add (word_add r (word(13 * i))) (word 6) /\
          read X9 s = word_add (word_add a (word(32 * i))) (word 16) /\
          read X10 s = word_sub (word 32) (word i) /\
          read X11 s = word 4096 /\
          read SP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 13 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyt0_pack x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (4--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; ADD_CLAUSES; WORD_ADD_0] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    MAP_EVERY (fun (k,m) ->
      SUBGOAL_THEN
       (subst [mk_small_numeral k,`k:num`; mk_small_numeral m,`m:num`]
        `read (memory :> bytes32 (word_add (word_add a (word (32 * i)))
                                  (word k))) s0 = x (8 * i + m)`)
       ASSUME_TAC THENL
       [REWRITE_TAC[LDP_FIX] THEN ASM_REWRITE_TAC[]; ALL_TAC])
     [20,5; 28,7] THEN
    ARM_STEPS_TAC EXEC (1--48) THEN
    T0_FULL_FINAL_TAC `x:num->int32`;

    (*** The loop exit, the check of the stack guard and the return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (5--27) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
