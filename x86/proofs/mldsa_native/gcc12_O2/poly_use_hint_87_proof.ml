(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the proof (see poly_use_hint_87_spec.ml).                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_use_hint_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* The end of one of the three paths through an iteration: the stored value  *)
(* equal to the spec under the conditions of the path, and the branch on the *)
(* offset back to the loop or out of it.                                     *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_87_PATH_END_TAC =
  SCALAR_LANE2_TAC `word_add (a:int64) (word(1 * 4 * i))` `(x:num->int32) i`
    `(y:num->int32) i` `mld_use_hint_32` [mld_use_hint_32] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration; the compiler has rotated it, so that it is     *)
(* entered by a jump to the loads, and each of the three paths (hint zero;   *)
(* low part positive; otherwise) has its own test of the offset, as in       *)
(* ENSURES_EVENTS_WHILE_UP2_TAC. The events of an iteration depend on the    *)
(* path, so the template of the events chooses between three meta-variables  *)
(* by the conditions of the branches, which each path instantiates with its  *)
(* case assumptions (PATH_DISCHARGE_TAC). The high part, in EDX, and the low *)
(* part, in EAX, whose sign the code tests, are replaced by their            *)
(* specifications as soon as they are computed (REG_LANE_TAC,                *)
(* REG32_LANE_TAC).                                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (x:num->int32) (y:num->int32) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil a h x y pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0
                 then f_ev_zero a h x y pc stackpointer returnaddress i
                 else if &0 < ival(mld_decompose_lo_32 (x i))
                 then f_ev_pos a h x y pc stackpointer returnaddress i
                 else f_ev_neg a h x y pc stackpointer returnaddress i))
          (f_ev_prol a h x y pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `h:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; mld_poly_use_hint_32;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, at the loads ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa87_poly_use_hint_loop1`
   `pc + mldsa87_poly_use_hint_loop1_exit3`
   `\i s. read RDI s = a /\ read R8 s = h /\ read RSI s = word(4 * i) /\
          read R9 s = word 4190208 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_32 (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, and the jump into the loop ***)

    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with its three paths ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    DISCH_TAC THEN
    VAL_INT64_TAC `4 * i` THEN INDEX4_ADDR_TAC THEN
    X86_STEPS_TAC EXEC (1--8) THEN
    REG_LANE_TAC `RDX` `(x:num->int32) i` `mld_decompose_hi_32`
      [DECOMPOSE_HI_32_ALT] THEN
    X86_STEPS_TAC EXEC (9--21) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [X86_STEPS_TAC EXEC (22--25) THEN USE_HINT_87_PATH_END_TAC;
      X86_STEPS_TAC EXEC (22--25) THEN
      REG32_LANE_TAC `RAX` `(x:num->int32) i` `mld_decompose_lo_32`
        [DECOMPOSE_LO_32_ALT; mld_ct_sel] THEN
      X86_STEPS_TAC EXEC (26--26) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[USE_HINT_GT_COND]) THEN
      BRANCH_CASES_TAC THEN
      X86_STEPS_TAC EXEC (27--32) THEN USE_HINT_87_PATH_END_TAC];

    (*** The return ***)

    FULL_PATHS_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
