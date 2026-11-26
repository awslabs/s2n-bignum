(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Row i of the product of the matrix A, sampled on demand, with a vector in *)
(* the NTT domain: the proof (see                                            *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml).                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_inline.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let ROWL87_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 1664 bytes is at stackpointer - 1664 (called s below). The   *)
(* function stores 64 bytes of registers, lowers sp by 96 and clears its low *)
(* 5 bits: the buffer of the seed, aligned to 32 bytes, is at s + 1504 or at *)
(* s + 1488 (the 1472 bytes below it are those of mldsa_poly_uniform). The   *)
(* code is simulated with the loops unrolled, in each case of the stack      *)
(* alignment: the seed and the termination hypothesis of each entry before   *)
(* its sampling, the product of the entry with polynomial j of the vector    *)
(* (the first into t, the others into the polynomial cur of the matrix), and *)
(* its sum into t as the lemmas of the inlined loops. The test of overlap    *)
(* of t and cur before each sum is decided by RL_ALIAS.                      *)
(* ------------------------------------------------------------------------- *)

let ROWL87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1504 1504 1488;;

let ROWL87_ALLOWED =
  [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `i:num`; `r:num`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let ROWL87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc ROWL87_EXEC
   name ilist ROWL87_ALLOWED n;;

let ROWL87_TEMPLATE = parse_term
 "\\(t:int64) (mat:int64) (v:int64) (i:num) (r:num) (guard:int64) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    if aligned 32 stackpointer
    then f_ev_a t mat v i r guard mf mc pc stackpointer returnaddress
    else f_ev_u t mat v i r guard mf mc pc stackpointer returnaddress:(uarch_event)list";;

(*** The instruction after each sampling: the seed, with the entry j, is   ***)
(*** stored by the two instructions before the call                         ***)

let ROWL87_SEED_TAC bf j sn n =
  MLD_LAZY_ROW_INDEX_TAC 8 THEN MLD_LAZY_ROW_SEED_TAC 8 bf j sn THEN
  MLD_LAZY_ROW_TERM_TAC 8 7 j THEN ARM_STEPS_TAC ROWL87_EXEC [n];;

(*** The decision of the test of overlap of t and cur ***)

let ROWL87_ALIAS_TAC =
  MP_TAC(SPECL [`t:int64`; `mat:int64`] RL_ALIAS) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th; COND_CLAUSES]))];;

let ROWL87_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN POLYVEC_SPLIT_TAC 7 THEN
  ARM_STEPS_TAC ROWL87_EXEC (1--7) THEN
  MEXP_BUFFER_TAC ROWL87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC ROWL87_EXEC [8] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL87_EXEC (9--24) THEN
  ROWL87_SEED_TAC bf 0 "s24" 25 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC ROWL87_EXEC (27--28) THEN
  ROWL87_CALL_TAC "H_PW1"
   [`read X19 s`; `read X21 s`; MLD_LAZY_ROW_ENTRY 0; MLD_LAZY_ROW_POLY 0;
    `pc:num`] 29 THEN
  ARM_STEPS_TAC ROWL87_EXEC (30--34) THEN ROWL87_SEED_TAC bf 1 "s34" 35 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 36 THEN
  ARM_STEPS_TAC ROWL87_EXEC (37--39) THEN
  ROWL87_CALL_TAC "H_PW2"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 1; MLD_LAZY_ROW_POLY 1;
    `pc:num`] 40 THEN
  ARM_STEPS_TAC ROWL87_EXEC (41--44) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD1"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 0; MLD_LAZY_ROW_PW 1;
    `pc:num`] 45 THEN
  ARM_STEPS_TAC ROWL87_EXEC (46--50) THEN ROWL87_SEED_TAC bf 2 "s50" 51 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 52 THEN
  ARM_STEPS_TAC ROWL87_EXEC (53--55) THEN
  ROWL87_CALL_TAC "H_PW3"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 2; MLD_LAZY_ROW_POLY 2;
    `pc:num`] 56 THEN
  ARM_STEPS_TAC ROWL87_EXEC (57--60) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD2"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 1; MLD_LAZY_ROW_PW 2;
    `pc:num`] 61 THEN
  ARM_STEPS_TAC ROWL87_EXEC (62--66) THEN ROWL87_SEED_TAC bf 3 "s66" 67 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 68 THEN
  ARM_STEPS_TAC ROWL87_EXEC (69--71) THEN
  ROWL87_CALL_TAC "H_PW4"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 3; MLD_LAZY_ROW_POLY 3;
    `pc:num`] 72 THEN
  ARM_STEPS_TAC ROWL87_EXEC (73--76) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD3"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 2; MLD_LAZY_ROW_PW 3;
    `pc:num`] 77 THEN
  ARM_STEPS_TAC ROWL87_EXEC (78--82) THEN ROWL87_SEED_TAC bf 4 "s82" 83 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 84 THEN
  ARM_STEPS_TAC ROWL87_EXEC (85--87) THEN
  ROWL87_CALL_TAC "H_PW5"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 4; MLD_LAZY_ROW_POLY 4;
    `pc:num`] 88 THEN
  ARM_STEPS_TAC ROWL87_EXEC (89--92) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD4"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 3; MLD_LAZY_ROW_PW 4;
    `pc:num`] 93 THEN
  ARM_STEPS_TAC ROWL87_EXEC (94--98) THEN ROWL87_SEED_TAC bf 5 "s98" 99 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 100 THEN
  ARM_STEPS_TAC ROWL87_EXEC (101--104) THEN
  ROWL87_CALL_TAC "H_PW6"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 5; MLD_LAZY_ROW_POLY 5;
    `pc:num`] 105 THEN
  ARM_STEPS_TAC ROWL87_EXEC (106--109) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD5"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 4; MLD_LAZY_ROW_PW 5;
    `pc:num`] 110 THEN
  ARM_STEPS_TAC ROWL87_EXEC (111--115) THEN ROWL87_SEED_TAC bf 6 "s115" 116 THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 117 THEN
  ARM_STEPS_TAC ROWL87_EXEC (118--121) THEN
  ROWL87_CALL_TAC "H_PW7"
   [`read X20 s`; `read X9 s`; MLD_LAZY_ROW_ENTRY 6; MLD_LAZY_ROW_POLY 6;
    `pc:num`] 122 THEN
  ARM_STEPS_TAC ROWL87_EXEC (123--126) THEN ROWL87_ALIAS_TAC THEN
  ROWL87_CALL_TAC "H_ADD6"
   [`read X19 s`; `read X20 s`; MLD_LAZY_ROW_ACC 5; MLD_LAZY_ROW_PW 6;
    `pc:num`] 127 THEN
  ARM_STEPS_TAC ROWL87_EXEC (128--132) THEN
  ROWL87_CALL_TAC "H_RED"
   [`read X19 s`; MLD_LAZY_ROW_ACC 6; `pc:num`] 133 THEN
  ARM_STEPS_TAC ROWL87_EXEC (134--137) THEN
  ARM_STEPS_TAC ROWL87_EXEC [138] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL87_EXEC (139--158) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_ROW_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_UNIF") THEN
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [RL87_PWM1,"H_PW1";
    RL87_PWM2,"H_PW2";
    RL87_PWM3,"H_PW3";
    RL87_PWM4,"H_PW4";
    RL87_PWM5,"H_PW5";
    RL87_PWM6,"H_PW6";
    RL87_PWM7,"H_PW7";
    RL87_ADD1,"H_ADD1";
    RL87_ADD2,"H_ADD2";
    RL87_ADD3,"H_ADD3";
    RL87_ADD4,"H_ADD4";
    RL87_ADD5,"H_ADD5";
    RL87_ADD6,"H_ADD6";
    RL87_RED,"H_RED"] THEN
  CONCRETIZE_F_EVENTS_TAC ROWL87_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst ROWL87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1664):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    ROWL87_CASE_TAC 1504;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    ROWL87_CASE_TAC 1488]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
