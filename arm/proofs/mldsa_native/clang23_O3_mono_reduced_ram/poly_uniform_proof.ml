(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed: the proof (see        *)
(* poly_uniform_spec.ml). The prologue realigns the stack pointer to 32      *)
(* bytes, which gives two cases (the stack pointer of the caller is a        *)
(* multiple of 32 bytes or not); the rest is PU_MAIN of                      *)
(* inline_uniform_main.ml, at the lowest address of the frame fr = sp - 240  *)
(* of the buffers, and the stack check and the epilogue.                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_uniform_main.ml";;

let PU_ALIGN288 = SAMPLING_ALIGN32_RULE 288;;

let PU_ALIGN272 = prove
 (`!sp:int64. aligned 16 sp /\ ~aligned 32 sp
              ==> aligned 32 (word_add sp (word 272)) /\
                  aligned 16 (word_add sp (word 272))`,
  REWRITE_TAC[SAMPLING_ALIGNED_16_32] THEN GEN_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let PU_TOP_ALLOWED =
  [`a:int64`; `seed:int64`; `M:num`; `guard:int64`; `mf:int64`; `mc:int64`;
   `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let PU_TOP_TEMPLATE = parse_term
 "\\(a:int64) (seed:int64) (M:num) (guard:int64) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    if aligned 32 stackpointer
    then f_ev_a a seed M guard mf mc pc stackpointer returnaddress
    else f_ev_u a seed M guard mf mc pc stackpointer returnaddress:(uarch_event)list";;

let PU_PU_NOV tm = SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL [NONOVERLAPPING_TAC; ALL_TAC];;

let PU_TOP_PREFIX_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_MAIN) th) "H_MAIN") THEN
  CONCRETIZE_F_EVENTS_TAC PU_TOP_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 1472):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD])) [`got_stack_chk_guard:num`; `got_memset:num`; `got_memcpy:num`] THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init") (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  FULL_INIT_TAC;;

let PU_TOP_ALIGNED_TAC =
  ARM_STEPS_TAC PU_EXEC (1--9) THEN
  RULE_ASSUM_TAC(fun th -> if find_substring (string_of_term (concl th)) "18446744073709551584" <> None then REWRITE_RULE[] (REWRITE_RULE[MP (SPEC `stackpointer:int64` PU_ALIGN288) (ASSUME `aligned 16 (stackpointer:int64)`); ASSUME `aligned 32 (stackpointer:int64)`] th) else th) THEN
  SUBGOAL_THEN `aligned 16 (word_add stackpointer (word 288):int64)` ASSUME_TAC THENL [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aligned 32 (word_add stackpointer (word 288):int64)` ASSUME_TAC THENL [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY PU_PU_NOV [`nonoverlapping (a:int64,1024) (word_add (word pc) (word 327672):int64,8)`; `nonoverlapping (a:int64,1024) (word_add (word pc) (word 327656):int64,8)`; `nonoverlapping (a:int64,1024) (word_add (word pc) (word 327632):int64,8)`;
   `nonoverlapping (a:int64,1024) (word_add stackpointer (word 48):int64,1328)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (seed:int64,34)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (word pc:int64,libmldsa_size)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (word_add (word pc) (word 327672):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (guard:int64,8)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (word_add (word pc) (word 327656):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (word_add (word pc) (word 327632):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 48):int64,1328) (ea:int64,el)`] THEN
  REMOVE_THEN "H_MAIN" (fun th -> ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `guard:int64`; `canary:int64`; `read X29 s`; `pc:num`; `word_sub (read SP s) (word 240)`] 10 THENL [(FULL_EXISTS_E2_TAC (ref PU_TOP_ALLOWED) ORELSE PU_E2_TAC (ref PU_TOP_ALLOWED)); LABEL_TAC "H_MAIN" th]) THEN
  ARM_STEPS_TAC PU_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PU_EXEC (12--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PU_SAFETY_TAC;;

let PU_TOP_UNALIGNED_TAC =
  ARM_STEPS_TAC PU_EXEC (1--9) THEN
  RULE_ASSUM_TAC(fun th -> if find_substring (string_of_term (concl th)) "18446744073709551584" <> None then REWRITE_RULE[] (REWRITE_RULE[MP (SPEC `stackpointer:int64` PU_ALIGN288) (ASSUME `aligned 16 (stackpointer:int64)`); EQF_INTRO(ASSUME `~aligned 32 (stackpointer:int64)`)] th) else th) THEN
  MP_TAC(MATCH_MP PU_ALIGN272 (CONJ (ASSUME `aligned 16 (stackpointer:int64)`) (ASSUME `~aligned 32 (stackpointer:int64)`))) THEN STRIP_TAC THEN
  MAP_EVERY PU_PU_NOV [`nonoverlapping (a:int64,1024) (word_add (word pc) (word 327672):int64,8)`; `nonoverlapping (a:int64,1024) (word_add (word pc) (word 327656):int64,8)`; `nonoverlapping (a:int64,1024) (word_add (word pc) (word 327632):int64,8)`;
   `nonoverlapping (a:int64,1024) (word_add stackpointer (word 32):int64,1328)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (seed:int64,34)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (word pc:int64,libmldsa_size)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (word_add (word pc) (word 327672):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (guard:int64,8)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (word_add (word pc) (word 327656):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (word_add (word pc) (word 327632):int64,8)`;
   `nonoverlapping (word_add stackpointer (word 32):int64,1328) (ea:int64,el)`] THEN
  REMOVE_THEN "H_MAIN" (fun th -> ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `guard:int64`; `canary:int64`; `read X29 s`; `pc:num`; `word_sub (read SP s) (word 240)`] 10 THENL [(FULL_EXISTS_E2_TAC (ref PU_TOP_ALLOWED) ORELSE PU_E2_TAC (ref PU_TOP_ALLOWED)); LABEL_TAC "H_MAIN" th]) THEN
  ARM_STEPS_TAC PU_EXEC (11--11) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PU_EXEC (12--31) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN PU_SAFETY_TAC;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  PU_TOP_PREFIX_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [PU_TOP_ALIGNED_TAC; PU_TOP_UNALIGNED_TAC]);;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;
