(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_65_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let MEXP65_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 336 bytes is at stackpointer + 4752 (the 4752 bytes below it *)
(* are the callee's), with the canary at stackpointer + 5080 and the four    *)
(* buffers at stackpointer + 4800 or + 4816. The code is simulated with the  *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x, and then the last    *)
(* two entries with mldsa_poly_uniform.                                      *)
(* ------------------------------------------------------------------------- *)

let MEXP65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 4831 4800 4816;;

let MEXP65_ALLOWED =
  [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let MEXP65_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MEXP65_EXEC "H_X4"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
    map (fun m -> let n = 4 * g + m in MEXP_SEED (n / 5) (n mod 5))
        (0--3) @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`])
   MEXP65_ALLOWED n;;

let MEXP65_SINGLE_CALL_TAC i j n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MEXP65_EXEC "H_ONE"
   [`read X0 s`; `read X1 s`; MEXP_SEED i j;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`]
   MEXP65_ALLOWED n;;

let MEXP65_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (1--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (6--8) THEN
  MEXP_BUFFER_TAC MEXP65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC MEXP65_EXEC (9--38) THEN
  MEXP_SETUP_TAC 6 5 `s38:armstate` THEN
  ARM_STEPS_TAC MEXP65_EXEC (39--105) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 0 0 `s105:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 0 1 `s105:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 0 2 `s105:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 0 3 `s105:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [106] THEN
  MEXP65_CALL_TAC 0 107 THEN
  ARM_STEPS_TAC MEXP65_EXEC (108--176) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 0 4 `s176:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 1 0 `s176:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 1 1 `s176:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 1 2 `s176:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [177] THEN
  MEXP65_CALL_TAC 1 178 THEN
  ARM_STEPS_TAC MEXP65_EXEC (179--247) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 1 3 `s247:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 1 4 `s247:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 2 0 `s247:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 2 1 `s247:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [248] THEN
  MEXP65_CALL_TAC 2 249 THEN
  ARM_STEPS_TAC MEXP65_EXEC (250--318) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 2 2 `s318:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 2 3 `s318:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 2 4 `s318:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 3 0 `s318:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [319] THEN
  MEXP65_CALL_TAC 3 320 THEN
  ARM_STEPS_TAC MEXP65_EXEC (321--389) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 3 1 `s389:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 3 2 `s389:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 3 3 `s389:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 3 4 `s389:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [390] THEN
  MEXP65_CALL_TAC 4 391 THEN
  ARM_STEPS_TAC MEXP65_EXEC (392--460) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 4 0 `s460:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 4 1 `s460:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 4 2 `s460:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 4 3 `s460:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [461] THEN
  MEXP65_CALL_TAC 5 462 THEN
  ARM_STEPS_TAC MEXP65_EXEC (463--531) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 4 4 `s531:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 5 0 `s531:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 5 1 `s531:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 5 2 `s531:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP65_EXEC [532] THEN
  MEXP65_CALL_TAC 6 533 THEN
  ARM_STEPS_TAC MEXP65_EXEC (534--539) THEN
  MEXP_INPUT_TAC b 5 3 `s539:armstate` THEN
  ARM_STEPS_TAC MEXP65_EXEC [540] THEN
  MEXP65_SINGLE_CALL_TAC 5 3 541 THEN
  ARM_STEPS_TAC MEXP65_EXEC (542--546) THEN
  MEXP_INPUT_TAC b 5 4 `s546:armstate` THEN
  ARM_STEPS_TAC MEXP65_EXEC [547] THEN
  MEXP65_SINGLE_CALL_TAC 5 4 548 THEN
  ARM_STEPS_TAC MEXP65_EXEC (549--551) THEN
  ARM_STEPS_TAC MEXP65_EXEC [552] THEN
  LIBC_PLT_TAC MEXP65_EXEC 552 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MEXP65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MEXP65_ALLOWED) 557 THEN
  ARM_STEPS_TAC MEXP65_EXEC [558] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP65_EXEC (559--568) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MEXP_JOIN_TAC 30; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
      "H_X4" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
      "H_ONE") THEN
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
              fst MEXP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5088):int64)` THEN
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
     (mk_const(r,[]))) (19--22) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [MEXP65_CASE_TAC 4800; MEXP65_CASE_TAC 4816]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
