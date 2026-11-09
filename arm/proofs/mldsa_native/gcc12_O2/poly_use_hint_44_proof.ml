(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the proof (see poly_use_hint_44_spec.ml).                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* The code tests the offset after its increment, X6 = 4 * (i + 1), against  *)
(* 1024 (as X6 + (2^64 - 1020) before the increment's result is compared).   *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_LOOP_TEST = prove
 (`!i. i < 256
       ==> (val(word_add (word(4 * i))
                         (word 18446744073709550596):int64) = 0 <=>
            ~(i + 1 < 256))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `4 * i < 1020` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `4 * i < 1020 ==> 4 * i < 18446744073709551616`;
    ARITH_RULE `4 * i < 1020
                ==> 4 * i + 18446744073709550596 < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The end of one of the three paths through an iteration: the stored value  *)
(* equal to the spec under the conditions of the path, and the branch on the *)
(* offset back to the loop or out of it.                                     *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_44_PATH_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE
   [MP (SPEC `i:num` USE_HINT_LOOP_TEST) (ASSUME `i < 256`)]) THEN
  SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
    `(y:num->int32) i` `mld_use_hint_88` [mld_use_hint_88] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(*** The test of the low part (B.GT after CMP with 0) as a comparison ***)

let USE_HINT_44_GT_COND = prove
 (`!w:int32.
     (~(val(word_sub (word_zx (word_zx w:int64):int32) (word 0)) = 0) /\
      (ival(word_sub (word_zx (word_zx w:int64):int32) (word 0)) < &0 <=>
       ~(ival(word_zx (word_zx w:int64):int32) - &0 =
         ival(word_sub (word_zx (word_zx w:int64):int32) (word 0))))) <=>
     &0 < ival w`,
  REWRITE_TAC[WORD_ZX_ZX_32_64_32; WORD_SUB_0; INT_SUB_RZERO; VAL_EQ_0] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM IVAL_EQ_0] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration; the compiler has rotated it, so that it is     *)
(* entered by a branch to the loads, and each of the three paths (hint zero; *)
(* low part positive; otherwise) has its own test of the offset, as in       *)
(* ENSURES_EVENTS_WHILE_UP2_TAC. The events of an iteration depend on the    *)
(* path, so the template of the events chooses between three meta-variables  *)
(* by the conditions of the branches, which each path instantiates with its  *)
(* case assumptions (PATH_DISCHARGE_TAC).                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (x:num->int32) (y:num->int32) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a h x y pc returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0 then f_ev_zero a h x y pc returnaddress i
                 else if &0 < ival(mld_decompose_lo_88 (x i))
                 then f_ev_pos a h x y pc returnaddress i
                 else f_ev_neg a h x y pc returnaddress i))
          (f_ev_prol a h x y pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `h:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; mld_poly_use_hint_88;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, at the loads ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa44_poly_use_hint_loop1`
   `pc + mldsa44_poly_use_hint_loop1_exit`
   `\i s. read X0 s = a /\ read X1 s = h /\ read X6 s = word(4 * i) /\
          read X10 s = word 4294776832 /\ read X11 s = word 11275 /\
          read X7 s = word 43 /\ read X9 s = word 4190208 /\
          read X8 s = word 4286586879 /\
          read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_88 (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, and the branch into the loop ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with its three paths ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_88` (concl th)))) THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (1--10) THEN
    REG_LANE_TAC `X2` `(x:num->int32) i` `mld_decompose_hi_88`
      [mld_decompose_hi_88; mld_ct_sel] THEN
    ARM_STEPS_TAC EXEC (11--19) THEN
    REG_LANE_TAC `X3` `(x:num->int32) i` `mld_decompose_lo_88`
      [DECOMPOSE_LO_88_ALT; mld_ct_sel] THEN
    ARM_STEPS_TAC EXEC (20--20) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC EXEC (21--24) THEN USE_HINT_44_PATH_END_TAC;
      ARM_STEPS_TAC EXEC (21--23) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[USE_HINT_44_GT_COND]) THEN
      BRANCH_CASES_TAC THEN
      ARM_STEPS_TAC EXEC (24--29) THEN USE_HINT_44_PATH_END_TAC];

    (*** The return ***)

    FULL_PATHS_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
