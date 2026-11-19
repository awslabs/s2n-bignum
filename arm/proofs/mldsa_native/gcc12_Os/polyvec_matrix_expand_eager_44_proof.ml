(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_44_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let MEXP44_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 352 bytes is at stackpointer + 4752 (the 4752 bytes below it *)
(* are the callee's), with the canary at stackpointer + 5096 and the four    *)
(* buffers at stackpointer + 4832 or + 4816. The code is simulated with the  *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x.                      *)
(* ------------------------------------------------------------------------- *)

let MEXP44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 4847 4832 4816;;

let MEXP44_ALLOWED =
  [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let MEXP44_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MEXP44_EXEC "H_X4"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
    map (fun m -> MEXP_SEED g m) (0--3) @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`])
   MEXP44_ALLOWED n;;

let MEXP44_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MEXP44_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP44_EXEC (4--7) THEN
  MEXP_BUFFER_TAC MEXP44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC MEXP44_EXEC (8--42) THEN
  MEXP_SETUP_TAC 4 4 `s42:armstate` THEN
  ARM_STEPS_TAC MEXP44_EXEC (43--92) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 0 0 `s92:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 0 1 `s92:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 0 2 `s92:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 0 3 `s92:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP44_EXEC [93] THEN
  MEXP44_CALL_TAC 0 94 THEN
  ARM_STEPS_TAC MEXP44_EXEC (95--148) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 1 0 `s148:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 1 1 `s148:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 1 2 `s148:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 1 3 `s148:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP44_EXEC [149] THEN
  MEXP44_CALL_TAC 1 150 THEN
  ARM_STEPS_TAC MEXP44_EXEC (151--204) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 2 0 `s204:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 2 1 `s204:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 2 2 `s204:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 2 3 `s204:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP44_EXEC [205] THEN
  MEXP44_CALL_TAC 2 206 THEN
  ARM_STEPS_TAC MEXP44_EXEC (207--260) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 3 0 `s260:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 3 1 `s260:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 3 2 `s260:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 3 3 `s260:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP44_EXEC [261] THEN
  MEXP44_CALL_TAC 3 262 THEN
  ARM_STEPS_TAC MEXP44_EXEC (263--267) THEN
  ARM_STEPS_TAC MEXP44_EXEC [268] THEN
  LIBC_PLT_TAC MEXP44_EXEC 268 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MEXP44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MEXP44_ALLOWED) 273 THEN
  ARM_STEPS_TAC MEXP44_EXEC [274] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP44_EXEC (275--285) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MEXP_JOIN_TAC 16; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
      "H_X4") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
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
              fst MEXP44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5104):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--25) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [MEXP44_CASE_TAC 4832; MEXP44_CASE_TAC 4816]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
