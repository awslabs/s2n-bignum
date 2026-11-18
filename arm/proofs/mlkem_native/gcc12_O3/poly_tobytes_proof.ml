(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O3/poly_tobytes_spec.ml";;


let TOBYTES_PACK = prove
 (TOBYTES_PACK_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 128
        ==> read (memory :> bytes(r,3 * k)) s =
            num_of_wordlist
             (MAP word_zx (SUB_LIST(0,2 * k) (l:int16 list)):(12 word)list)`
   (MP_TAC o SPEC `128`) THENL
   [ALL_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `LENGTH(l:int16 list) = 256`)) THEN
    REWRITE_TAC[SUB_LIST_LENGTH]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; MAP; num_of_wordlist;
                READ_MEMORY_BYTES_TRIVIAL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 128` THEN ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[ADD1; ARITH_RULE `3 * (k + 1) = ((3 * k + 1) + 1) + 1`;
              ARITH_RULE `2 * (k + 1) = 2 * k + 2`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE `(3 * k + 1) + 1 = 3 * k + 2`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SUB_LIST_0_SNOC2;
               ARITH_RULE `SUC k <= 128 ==> 2 * k + 2 <= 256`] THEN
  REWRITE_TAC[MAP_APPEND; MAP; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
              LENGTH_SUB_LIST; num_of_wordlist] THEN
  SUBGOAL_THEN `val(EL (2 * k) (l:int16 list)) < 4096` MP_TAC THENL
   [UNDISCH_TAC `ALL (\x. val x < 4096) (l:int16 list)` THEN
    REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `2 * k`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC k <= 128 ==> MIN (2 * k) 256 = 2 * k`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 3 * k = 24 * k`;
              ARITH_RULE `12 * 2 * k = 24 * k`;
              ARITH_RULE `8 * (3 * k + 1) = 24 * k + 8`;
              ARITH_RULE `8 * (3 * k + 2) = 24 * k + 16`; EXP_ADD] THEN
  DISCH_TAC THEN MATCH_MP_TAC(NUM_RING
   `v0 + 2 EXP 8 * v1 + 2 EXP 16 * v2 = w0 + 2 EXP 12 * w1
    ==> ((n + a * v0) + (a * 2 EXP 8) * v1) + (a * 2 EXP 16) * v2 =
        n + a * (w0 + 2 EXP 12 * (w1 + 2 EXP 12 * 0))`) THEN
  UNDISCH_TAC `val(EL (2 * k) (l:int16 list)) < 4096` THEN
  SPEC_TAC(`EL (2 * k + 1) (l:int16 list)`, `t1:int16`) THEN
  SPEC_TAC(`EL (2 * k) (l:int16 list)`, `t0:int16`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 16 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Without the conditions on l, only the control flow matters ***)

  ASM_CASES_TAC `LENGTH(l:int16 list) = 256 /\ ALL (\x. val x < 4096) l`
  THENL
   [ALL_TAC;
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
    ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (6--125) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  TOBYTES_INPUT_TAC THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC [k] THEN
    TOBYTES_SIMD_TAC) (6--125) THEN
  TOBYTES_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The bytes of each group of two coefficients ***)

  MATCH_MP_TAC TOBYTES_PACK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (6--125) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN

  (*** The input as w j, whatever l is ***)

  SUBGOAL_THEN
   `?w:num->int16.
      !j. j < 256
          ==> read (memory :> bytes16 (word_add a (word(2 * j)))) s0 = w j`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\j. read (memory :> bytes16 (word_add a (word(2 * j)))) s0` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH(l:int16 list) = 256 ==> !j. j < 256 ==> EL j l = (w:num->int16) j`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `read (memory :> bytes16 (word_add a (word(2 * j)))) s0` THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `j:num`; `s0:armstate`]
                   READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
      ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `w:num->int16` (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `w:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOBYTES_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `384` `a:int64` `512` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O3_EXEC [k] THEN
    TOBYTES_SIMD_TAC) (6--125) THEN
  TOBYTES_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** Under the conditions on l, w j = EL j l, and the bytes as before ***)

  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) && free_in `EL:num->int16 list->int16` (concl th)
    then ASSUME_TAC(MP th (ASSUME `LENGTH(l:int16 list) = 256`))
    else NO_TAC) THEN
  MATCH_MP_TAC TOBYTES_PACK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `EL:num->int16 list->int16` (concl th)
    then REWRITE_TAC(map (fun j ->
           MP (SPEC (mk_small_numeral j) th)
              (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                                    (mk_small_numeral j) `256`)))) (0--255))
    else NO_TAC) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;
