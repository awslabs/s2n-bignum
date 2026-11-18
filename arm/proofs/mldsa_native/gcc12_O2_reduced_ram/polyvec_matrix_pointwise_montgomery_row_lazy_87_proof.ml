(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Row i of the product of the matrix A, sampled on demand, with a vector in *)
(* the NTT domain: the proof (see                                            *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml).                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let ROWL87_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 160 bytes is at stackpointer + 1392 (the 1392 bytes below it *)
(* are those of mldsa_poly_uniform), with the saved registers at             *)
(* stackpointer + 1392, the canary at stackpointer + 1544 and the buffer of  *)
(* the seed, aligned to 32 bytes, at stackpointer + 1472 or + 1456. The code *)
(* is simulated with the loop unrolled, in each case of the stack alignment, *)
(* with the calls at the steps of the schedule given by the code: the seed   *)
(* and the termination hypothesis of each entry before its sampling, then    *)
(* the product with polynomial j of the vector and its addition to the       *)
(* result.                                                                   *)
(* ------------------------------------------------------------------------- *)

let ROWL87_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1487 1472 1456;;

let ROWL87_ALLOWED =
  [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `i:num`; `r:num`;
   `guard:int64`; `mf:int64`; `stackpointer:int64`; `returnaddress:int64`];;

let ROWL87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc ROWL87_EXEC name ilist
   ROWL87_ALLOWED n;;

let ROWL87_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN POLYVEC_SPLIT_TAC 7 THEN
  ARM_STEPS_TAC ROWL87_EXEC (1--8) THEN
  MEXP_BUFFER_TAC ROWL87_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC ROWL87_EXEC (9--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL87_EXEC (13--23) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 0 "s23" THEN MLD_LAZY_ROW_TERM_TAC 8 7 0 THEN
  ARM_STEPS_TAC ROWL87_EXEC [24] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC ROWL87_EXEC (26--28) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 0; MLD_LAZY_ROW_POLY 0;
    `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC ROWL87_EXEC (30--35) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 1 "s35" THEN MLD_LAZY_ROW_TERM_TAC 8 7 1 THEN
  ARM_STEPS_TAC ROWL87_EXEC [36] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  ARM_STEPS_TAC ROWL87_EXEC (38--40) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 1; MLD_LAZY_ROW_POLY 1;
    `pc:num`; `read X30 s`] 41 THEN
  ARM_STEPS_TAC ROWL87_EXEC (42--45) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 0; MLD_LAZY_ROW_PW 1;
    `pc:num`; `read X30 s`] 46 THEN
  ARM_STEPS_TAC ROWL87_EXEC (47--53) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 2 "s53" THEN MLD_LAZY_ROW_TERM_TAC 8 7 2 THEN
  ARM_STEPS_TAC ROWL87_EXEC [54] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 55 THEN
  ARM_STEPS_TAC ROWL87_EXEC (56--58) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 2; MLD_LAZY_ROW_POLY 2;
    `pc:num`; `read X30 s`] 59 THEN
  ARM_STEPS_TAC ROWL87_EXEC (60--63) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 1; MLD_LAZY_ROW_PW 2;
    `pc:num`; `read X30 s`] 64 THEN
  ARM_STEPS_TAC ROWL87_EXEC (65--71) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 3 "s71" THEN MLD_LAZY_ROW_TERM_TAC 8 7 3 THEN
  ARM_STEPS_TAC ROWL87_EXEC [72] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 73 THEN
  ARM_STEPS_TAC ROWL87_EXEC (74--76) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 3; MLD_LAZY_ROW_POLY 3;
    `pc:num`; `read X30 s`] 77 THEN
  ARM_STEPS_TAC ROWL87_EXEC (78--81) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 2; MLD_LAZY_ROW_PW 3;
    `pc:num`; `read X30 s`] 82 THEN
  ARM_STEPS_TAC ROWL87_EXEC (83--89) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 4 "s89" THEN MLD_LAZY_ROW_TERM_TAC 8 7 4 THEN
  ARM_STEPS_TAC ROWL87_EXEC [90] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 4`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 91 THEN
  ARM_STEPS_TAC ROWL87_EXEC (92--94) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 4; MLD_LAZY_ROW_POLY 4;
    `pc:num`; `read X30 s`] 95 THEN
  ARM_STEPS_TAC ROWL87_EXEC (96--99) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 3; MLD_LAZY_ROW_PW 4;
    `pc:num`; `read X30 s`] 100 THEN
  ARM_STEPS_TAC ROWL87_EXEC (101--107) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 5 "s107" THEN MLD_LAZY_ROW_TERM_TAC 8 7 5 THEN
  ARM_STEPS_TAC ROWL87_EXEC [108] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 5`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 109 THEN
  ARM_STEPS_TAC ROWL87_EXEC (110--112) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 5; MLD_LAZY_ROW_POLY 5;
    `pc:num`; `read X30 s`] 113 THEN
  ARM_STEPS_TAC ROWL87_EXEC (114--117) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 4; MLD_LAZY_ROW_PW 5;
    `pc:num`; `read X30 s`] 118 THEN
  ARM_STEPS_TAC ROWL87_EXEC (119--125) THEN
  MLD_LAZY_ROW_INDEX_TAC 8 THEN
  MLD_LAZY_ROW_SEED_TAC 8 bf 6 "s125" THEN MLD_LAZY_ROW_TERM_TAC 8 7 6 THEN
  ARM_STEPS_TAC ROWL87_EXEC [126] THEN
  ROWL87_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 6`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 127 THEN
  ARM_STEPS_TAC ROWL87_EXEC (128--130) THEN
  ROWL87_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 6; MLD_LAZY_ROW_POLY 6;
    `pc:num`; `read X30 s`] 131 THEN
  ARM_STEPS_TAC ROWL87_EXEC (132--135) THEN
  ROWL87_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 5; MLD_LAZY_ROW_PW 6;
    `pc:num`; `read X30 s`] 136 THEN
  ARM_STEPS_TAC ROWL87_EXEC (137--140) THEN
  ROWL87_CALL_TAC "H_RED"
   [`read X0 s`; MLD_LAZY_ROW_ACC 6; `pc:num`; `read X30 s`] 141 THEN
  ARM_STEPS_TAC ROWL87_EXEC (142--145) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL87_EXEC (146--156) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_ROW_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL th)
     "H_UNIF") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_PW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_ADD_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL "H_RED" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(t:int64) (mat:int64) (v:int64) (i:num) (r:num) (guard:int64)
     (mf:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     if aligned 32 stackpointer
     then f_ev_a t mat v i r guard mf pc stackpointer returnaddress
     else f_ev_u t mat v i r guard mf pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst ROWL87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1552):int64)` THEN
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
     (mk_const(r,[]))) (19--25) THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    ROWL87_CASE_TAC 1472;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    ROWL87_CASE_TAC 1456]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
