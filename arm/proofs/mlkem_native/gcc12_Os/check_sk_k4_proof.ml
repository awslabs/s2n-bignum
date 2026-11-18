(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/check_sk_k4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/sha3_256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/ct_memcmp_1_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The buffer for the hash is aligned to 32 bytes within the stack frame, so *)
(* its address depends on whether the stack pointer is a multiple of 32 or   *)
(* just of 16.                                                               *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let CHECK_SK_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 607)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 576 else 592))`,
  REWRITE_TAC[CHECK_SK_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let CHECK_SK_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 576 else 592))`;;

let CHECK_SK_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 607))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 576 else 592))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECK_SK_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The callees.                                                              *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_MEMCMP_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* The setup, with bounds on the offset of the buffer.                       *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 640):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `576 <= (if aligned 32 (stackpointer:int64) then 576 else 592) /\
    (if aligned 32 (stackpointer:int64) then 576 else 592) <= 592`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20`;;

(*** The GOT entries in the form in the preconditions of the callees ***)

let CHECK_SK_GOT_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
           `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
           (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(*** The result: both outcomes of the comparison of the hashes ***)

let CHECK_SK_RESULT_TAC =
  W(fun (_,w) ->
    SPEC_TAC(find_term (fun t -> is_eq t && lhs t = `h:num`) w,`c:bool`)) THEN
  GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN
  CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The correctness proof. The hash is stored in the buffer at the aligned    *)
(* address of the frame, compared with the stored hash and zeroed.           *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`sk:int64`; `ek:byte list`; `h:num`; `guard:int64`; `mf:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 640 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  CHECK_SK_SETUP_TAC;;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CHECK_SK_INTRO_TAC THEN ENSURES_INIT_TAC "s0" THEN

  (*** Saving the registers and the stack guard, and the hash ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (5--8) THEN
  CHECK_SK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (9--14) THEN
  CHECK_SK_GOT_TAC THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `mf:int64`;
    `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 15 THEN

  (*** The comparison and the zeroing of the buffer ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (16--19) THEN
  LOCAL_MEMCMP_TAC
   [`read X0 s`; `read X1 s`; `32`; `h:num`; `num_of_bytelist(sha3_256 ek)`;
    `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (21--26) THEN
  CHECK_SK_GOT_TAC THEN
  LOCAL_ZEROIZE_TAC
   [`read X0 s`; `32`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 27 THEN

  (*** The stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC [28] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (29--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECK_SK_RESULT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The combined correctness, constant-time and memory safety proof, from the *)
(* combined theorems of the callees, except for mlk_zeroize_2, whose result *)
(* is not needed.                                                            *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_ALLOWED =
  [`pc:num`; `sk:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let CHECK_SK_CALL_TAC name ilist n =
  CHECK_SK_GOT_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref CHECK_SK_ALLOWED); LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE
        (CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th))) "H_ZEROIZE") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_SHA3_256") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_MEMCMP" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CHECK_SK_SETUP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (5--8) THEN
  CHECK_SK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (9--14) THEN
  CHECK_SK_CALL_TAC "H_SHA3_256"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `ek:byte list`;
    `1568`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (16--19) THEN
  CHECK_SK_CALL_TAC "H_MEMCMP"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `32`; `h:num`;
    `num_of_bytelist(sha3_256 ek)`; `pc:num`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (21--26) THEN
  CHECK_SK_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `pc:num`; `read SP s`;
    `read X30 s`] 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC [28] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (29--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [CHECK_SK_RESULT_TAC; DISCHARGE_SAFETY_PROPERTY_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety proof, from the corresponding         *)
(* theorems of the callees.                                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_ZEROIZE_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE th)
     "H_ZEROIZE") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_SHA3_256_GCC12_OS_IMAGE_SUBROUTINE_SAFE th)
     "H_SHA3_256") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_CT_MEMCMP_1_GCC12_OS_IMAGE_SUBROUTINE_SAFE "H_MEMCMP" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CHECK_SK_SETUP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (5--8) THEN
  CHECK_SK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (9--14) THEN
  CHECK_SK_CALL_TAC "H_SHA3_256"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
    `1568`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 15 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (16--19) THEN
  CHECK_SK_CALL_TAC "H_MEMCMP"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `32`; `pc:num`;
    `read X30 s`] 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (21--26) THEN
  CHECK_SK_CALL_TAC "H_ZEROIZE"
   [`e:(uarch_event)list`; `read X0 s`; `32`; `pc:num`; `read SP s`;
    `read X30 s`] 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC [28] THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K4_GCC12_OS_EXEC (29--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

