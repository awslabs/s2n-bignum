(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_65_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let MEXP65_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 336 bytes is at stackpointer + 4720 (the 4720 bytes below it *)
(* are the callees'), with the canary at stackpointer + 5048 and the four    *)
(* buffers at stackpointer + 4768 or + 4784. The code is simulated with the  *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x, and then the         *)
(* last two entries with mldsa_poly_uniform.                                 *)
(* ------------------------------------------------------------------------- *)

let MEXP65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 4799 4768 4784;;

let MEXP65_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MEXP65_EXEC "H_X4"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
    map (fun m -> let n = 4 * g + m in MEXP_SEED (n / 5) (n mod 5))
        (0--3) @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`])
   [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `guard:int64`; `mf:int64`;
    `stackpointer:int64`; `returnaddress:int64`] n;;

let MEXP65_SINGLE_CALL_TAC i j n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc MEXP65_EXEC "H_ONE"
   [`read X0 s`; `read X1 s`; MEXP_SEED i j;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `guard:int64`; `mf:int64`;
    `stackpointer:int64`; `returnaddress:int64`] n;;

let MEXP65_GROUP_TAC b g =
  let s0 = 38 + 76 * g in
  let st = mk_var("s"^string_of_int (s0 + 71),`:armstate`) in
  ARM_STEPS_TAC MEXP65_EXEC (s0--(s0 + 71)) THEN
  MAP_EVERY (fun m -> let n = 4 * g + m in
                      MEXP_INPUT_TAC (b + 64 * m) (n / 5) (n mod 5) st)
   (0--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [s0 + 72] THEN
  MEXP65_CALL_TAC g (s0 + 73) THEN
  ARM_STEPS_TAC MEXP65_EXEC ((s0 + 74)--(s0 + 75));;

let MEXP65_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (3--8) THEN
  MEXP_BUFFER_TAC MEXP65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC MEXP65_EXEC (9--13) THEN
  MAP_EVERY (fun m ->
    ARM_STEPS_TAC MEXP65_EXEC ((14 + 5 * m)--(17 + 5 * m)) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MEXP65_EXEC [18 + 5 * m]) (0--3) THEN
  ARM_STEPS_TAC MEXP65_EXEC (34--37) THEN
  MEXP_SETUP_TAC 6 5 `s37:armstate` THEN
  MAP_EVERY (MEXP65_GROUP_TAC b) (0--6) THEN
  ARM_STEPS_TAC MEXP65_EXEC (570--573) THEN
  MEXP_INPUT_TAC b 5 3 `s573:armstate` THEN
  ARM_STEPS_TAC MEXP65_EXEC [574] THEN MEXP65_SINGLE_CALL_TAC 5 3 575 THEN
  ARM_STEPS_TAC MEXP65_EXEC (576--580) THEN
  MEXP_INPUT_TAC b 5 4 `s580:armstate` THEN
  ARM_STEPS_TAC MEXP65_EXEC [581] THEN MEXP65_SINGLE_CALL_TAC 5 4 582 THEN
  ARM_STEPS_TAC MEXP65_EXEC (583--592) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (593--602) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MEXP_JOIN_TAC 30; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
      "H_X4" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
      "H_ONE") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(mat:int64) (rho:int64) (r:num) (guard:int64) (mf:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
     if aligned 32 stackpointer
     then f_ev_a mat rho r guard mf pc stackpointer returnaddress
     else f_ev_u mat rho r guard mf pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MEXP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5056):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--23) THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [MEXP65_CASE_TAC 4768; MEXP65_CASE_TAC 4784]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
