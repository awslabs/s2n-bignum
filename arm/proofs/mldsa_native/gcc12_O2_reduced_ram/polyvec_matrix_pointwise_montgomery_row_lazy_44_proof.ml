(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Row i of the product of the matrix A, sampled on demand, with a vector in *)
(* the NTT domain: the proof (see                                            *)
(* polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml).                 *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_lazy_matrix.ml";;

let ROWL44_EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC;;

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

let ROWL44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 1487 1472 1456;;

let ROWL44_ALLOWED =
  [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `i:num`; `r:num`;
   `guard:int64`; `mf:int64`; `stackpointer:int64`; `returnaddress:int64`];;

let ROWL44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc ROWL44_EXEC name ilist
   ROWL44_ALLOWED n;;

let ROWL44_CASE_TAC bf =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match []
      `read (memory :> bytes(word_add mat (word 1024),32)) s = n`) o concl)) THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add mat (word 1024)) (word 16):int64 =
                          word_add mat (word 1040)`] THEN
  STRIP_TAC THEN MLD_LAZY_RBOUND_TAC "s0" THEN POLYVEC_SPLIT_TAC 4 THEN
  ARM_STEPS_TAC ROWL44_EXEC (1--7) THEN
  MEXP_BUFFER_TAC ROWL44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC ROWL44_EXEC (8--12) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL44_EXEC (13--23) THEN
  MLD_LAZY_ROW_INDEX_TAC 4 THEN
  MLD_LAZY_ROW_SEED_TAC 4 bf 0 "s23" THEN MLD_LAZY_ROW_TERM_TAC 4 4 0 THEN
  ARM_STEPS_TAC ROWL44_EXEC [24] THEN
  ROWL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 0`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC ROWL44_EXEC (26--28) THEN
  ROWL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 0; MLD_LAZY_ROW_POLY 0;
    `pc:num`; `read X30 s`] 29 THEN
  ARM_STEPS_TAC ROWL44_EXEC (30--34) THEN
  MLD_LAZY_ROW_INDEX_TAC 4 THEN
  MLD_LAZY_ROW_SEED_TAC 4 bf 1 "s34" THEN MLD_LAZY_ROW_TERM_TAC 4 4 1 THEN
  ARM_STEPS_TAC ROWL44_EXEC [35] THEN
  ROWL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 1`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 36 THEN
  ARM_STEPS_TAC ROWL44_EXEC (37--39) THEN
  ROWL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 1; MLD_LAZY_ROW_POLY 1;
    `pc:num`; `read X30 s`] 40 THEN
  ARM_STEPS_TAC ROWL44_EXEC (41--44) THEN
  ROWL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 0; MLD_LAZY_ROW_PW 1;
    `pc:num`; `read X30 s`] 45 THEN
  ARM_STEPS_TAC ROWL44_EXEC (46--52) THEN
  MLD_LAZY_ROW_INDEX_TAC 4 THEN
  MLD_LAZY_ROW_SEED_TAC 4 bf 2 "s52" THEN MLD_LAZY_ROW_TERM_TAC 4 4 2 THEN
  ARM_STEPS_TAC ROWL44_EXEC [53] THEN
  ROWL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 2`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 54 THEN
  ARM_STEPS_TAC ROWL44_EXEC (55--57) THEN
  ROWL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 2; MLD_LAZY_ROW_POLY 2;
    `pc:num`; `read X30 s`] 58 THEN
  ARM_STEPS_TAC ROWL44_EXEC (59--62) THEN
  ROWL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 1; MLD_LAZY_ROW_PW 2;
    `pc:num`; `read X30 s`] 63 THEN
  ARM_STEPS_TAC ROWL44_EXEC (64--70) THEN
  MLD_LAZY_ROW_INDEX_TAC 4 THEN
  MLD_LAZY_ROW_SEED_TAC 4 bf 3 "s70" THEN MLD_LAZY_ROW_TERM_TAC 4 4 3 THEN
  ARM_STEPS_TAC ROWL44_EXEC [71] THEN
  ROWL44_CALL_TAC "H_UNIF"
   [`read X0 s`; `read X1 s`; `mld_matrix_seed r i 3`; `guard:int64`;
    `pc:num`; `read SP s`; `read X30 s`] 72 THEN
  ARM_STEPS_TAC ROWL44_EXEC (73--75) THEN
  ROWL44_CALL_TAC "H_PW"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ENTRY 3; MLD_LAZY_ROW_POLY 3;
    `pc:num`; `read X30 s`] 76 THEN
  ARM_STEPS_TAC ROWL44_EXEC (77--80) THEN
  ROWL44_CALL_TAC "H_ADD"
   [`read X0 s`; `read X1 s`; MLD_LAZY_ROW_ACC 2; MLD_LAZY_ROW_PW 3;
    `pc:num`; `read X30 s`] 81 THEN
  ARM_STEPS_TAC ROWL44_EXEC (82--85) THEN
  ROWL44_CALL_TAC "H_RED"
   [`read X0 s`; MLD_LAZY_ROW_ACC 3; `pc:num`; `read X30 s`] 86 THEN
  ARM_STEPS_TAC ROWL44_EXEC (87--90) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC ROWL44_EXEC (91--101) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MLD_LAZY_ROW_POST_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
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
              fst ROWL44_EXEC] THEN
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
    ROWL44_CASE_TAC 1472;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    ROWL44_CASE_TAC 1456]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;
