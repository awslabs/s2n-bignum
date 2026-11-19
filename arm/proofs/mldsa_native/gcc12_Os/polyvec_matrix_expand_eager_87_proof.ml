(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the proof (see                          *)
(* polyvec_matrix_expand_eager_87_spec.ml).                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_matrix.ml";;

let MEXP87_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 336 bytes is at stackpointer + 4752 (the 4752 bytes below it *)
(* are the callee's), with the canary at stackpointer + 5080 and the four    *)
(* buffers at stackpointer + 4800 or + 4816. The code is simulated with the  *)
(* loops unrolled: the copies of rho, and for each group of four entries     *)
(* their indices and the call of mldsa_poly_uniform_4x.                      *)
(* ------------------------------------------------------------------------- *)

let MEXP87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 4831 4800 4816;;

let MEXP87_ALLOWED =
  [`pc:num`; `mat:int64`; `rho:int64`; `r:num`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let MEXP87_CALL_TAC g n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc MEXP87_EXEC "H_X4"
   ([`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`] @
    map (fun m -> let n = 4 * g + m in MEXP_SEED (n / 7) (n mod 7))
        (0--3) @
    [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`])
   MEXP87_ALLOWED n;;

let MEXP87_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  ARM_STEPS_TAC MEXP87_EXEC (1--5) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP87_EXEC (6--8) THEN
  MEXP_BUFFER_TAC MEXP87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC MEXP87_EXEC (9--38) THEN
  MEXP_SETUP_TAC 8 7 `s38:armstate` THEN
  ARM_STEPS_TAC MEXP87_EXEC (39--97) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 0 0 `s97:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 0 1 `s97:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 0 2 `s97:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 0 3 `s97:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [98] THEN
  MEXP87_CALL_TAC 0 99 THEN
  ARM_STEPS_TAC MEXP87_EXEC (100--160) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 0 4 `s160:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 0 5 `s160:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 0 6 `s160:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 1 0 `s160:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [161] THEN
  MEXP87_CALL_TAC 1 162 THEN
  ARM_STEPS_TAC MEXP87_EXEC (163--223) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 1 1 `s223:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 1 2 `s223:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 1 3 `s223:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 1 4 `s223:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [224] THEN
  MEXP87_CALL_TAC 2 225 THEN
  ARM_STEPS_TAC MEXP87_EXEC (226--286) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 1 5 `s286:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 1 6 `s286:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 2 0 `s286:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 2 1 `s286:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [287] THEN
  MEXP87_CALL_TAC 3 288 THEN
  ARM_STEPS_TAC MEXP87_EXEC (289--349) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 2 2 `s349:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 2 3 `s349:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 2 4 `s349:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 2 5 `s349:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [350] THEN
  MEXP87_CALL_TAC 4 351 THEN
  ARM_STEPS_TAC MEXP87_EXEC (352--412) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 2 6 `s412:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 3 0 `s412:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 3 1 `s412:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 3 2 `s412:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [413] THEN
  MEXP87_CALL_TAC 5 414 THEN
  ARM_STEPS_TAC MEXP87_EXEC (415--475) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 3 3 `s475:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 3 4 `s475:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 3 5 `s475:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 3 6 `s475:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [476] THEN
  MEXP87_CALL_TAC 6 477 THEN
  ARM_STEPS_TAC MEXP87_EXEC (478--538) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 4 0 `s538:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 4 1 `s538:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 4 2 `s538:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 4 3 `s538:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [539] THEN
  MEXP87_CALL_TAC 7 540 THEN
  ARM_STEPS_TAC MEXP87_EXEC (541--601) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 4 4 `s601:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 4 5 `s601:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 4 6 `s601:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 5 0 `s601:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [602] THEN
  MEXP87_CALL_TAC 8 603 THEN
  ARM_STEPS_TAC MEXP87_EXEC (604--664) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 5 1 `s664:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 5 2 `s664:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 5 3 `s664:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 5 4 `s664:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [665] THEN
  MEXP87_CALL_TAC 9 666 THEN
  ARM_STEPS_TAC MEXP87_EXEC (667--727) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 5 5 `s727:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 5 6 `s727:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 6 0 `s727:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 6 1 `s727:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [728] THEN
  MEXP87_CALL_TAC 10 729 THEN
  ARM_STEPS_TAC MEXP87_EXEC (730--790) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 6 2 `s790:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 6 3 `s790:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 6 4 `s790:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 6 5 `s790:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [791] THEN
  MEXP87_CALL_TAC 11 792 THEN
  ARM_STEPS_TAC MEXP87_EXEC (793--853) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 6 6 `s853:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 7 0 `s853:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 7 1 `s853:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 7 2 `s853:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [854] THEN
  MEXP87_CALL_TAC 12 855 THEN
  ARM_STEPS_TAC MEXP87_EXEC (856--916) THEN
  MEXP_INPUT_TAC (b + 64 * 0) 7 3 `s916:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 1) 7 4 `s916:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 2) 7 5 `s916:armstate` THEN
  MEXP_INPUT_TAC (b + 64 * 3) 7 6 `s916:armstate` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  ARM_STEPS_TAC MEXP87_EXEC [917] THEN
  MEXP87_CALL_TAC 13 918 THEN
  ARM_STEPS_TAC MEXP87_EXEC (919--923) THEN
  ARM_STEPS_TAC MEXP87_EXEC [924] THEN
  LIBC_PLT_TAC MEXP87_EXEC 924 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MEXP87_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref MEXP87_ALLOWED) 929 THEN
  ARM_STEPS_TAC MEXP87_EXEC [930] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MEXP87_EXEC (931--940) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MEXP_JOIN_TAC 56; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
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
              fst MEXP87_EXEC] THEN
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
   [MEXP87_CASE_TAC 4800; MEXP87_CASE_TAC 4816]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_OS_IMAGE_SUBROUTINE_FULL)
        th)));;
