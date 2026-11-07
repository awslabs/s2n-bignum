(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O3/basemul_k3_spec.ml";;


let MOD_2N_CASES = prove
 (MOD_2N_CASES_STMT,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let WORD_SUB_FLAG_64 = prove
 (WORD_SUB_FLAG_64_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  MP_TAC(ISPEC `x:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `y:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let BASEMUL_ALIAS = prove
 (BASEMUL_ALIAS_STMT,
  let n = `18446744073709551616` in
  let wit_tac (i,j) =
    MAP_EVERY EXISTS_TAC [i; j] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    W(fun (asl,w) -> let l,r = dest_eq w in
       MP_TAC(SPECL [lhand l; n] MOD_2N_CASES) THEN
       MP_TAC(SPECL [lhand r; n] MOD_2N_CASES)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_SUB_FLAG_64; NONOVERLAPPING_CLAUSES;
              nonoverlapping_modulo] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `dst:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `bc:int64` VAL_BOUND_64) THEN
  SPEC_TAC(`val(dst:int64)`,`d:num`) THEN
  SPEC_TAC(`val(bc:int64)`,`b:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b + m:num`; n] MOD_2N_CASES) THEN
  MP_TAC(SPECL [`d + 512`; n] MOD_2N_CASES) THEN
  REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_CASES_TAC `d + 512 < 18446744073709551616` THEN
  ASM_CASES_TAC `b + m < 18446744073709551616` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_exists(rand(concl th)))) THEN
  REWRITE_TAC[CONG] THEN ASM_CASES_TAC `d:num <= b` THEN
  FIRST(map wit_tac
   [`b - d:num`,`0`; `0`,`d - b:num`; `(b + 18446744073709551616) - d`,`0`;
    `0`,`(d + 18446744073709551616) - b`;
    `18446744073709551615 - d`,`18446744073709551615 - b`]));;

let BM_ADDR_A = prove
 (BM_ADDR_A_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_B = prove
 (BM_ADDR_B_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_C = prove
 (BM_ADDR_C_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_D = prove
 (BM_ADDR_D_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_B2 = prove
 (BM_ADDR_B2_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_D2 = prove
 (BM_ADDR_D2_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_E = prove
 (BM_ADDR_E_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_F = prove
 (BM_ADDR_F_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 48 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_DREG_TAC "d8_init" `D8` THEN
  ENSURES_PRESERVED_DREG_TAC "d9_init" `D9` THEN
  ENSURES_PRESERVED_DREG_TAC "d10_init" `D10` THEN
  ENSURES_PRESERVED_DREG_TAC "d11_init" `D11` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_WHILE_UP_TAC `16`
   `pc + mlkem768_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem768_polyvec_basemul_acc_montgomery_cached_loop1_test`
   basemul_k3_inv THEN
  REPEAT CONJ_TAC THENL
     [ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_CONSTANTS) THEN
    MP_TAC(SPECL [`dst:int64`; `srcBt:int64`; `768`] BASEMUL_ALIAS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ARITH_TAC;
                  DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--8) THEN
    FIRST_X_ASSUM(fun th -> if is_cond(concl th) then
    RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (9--11) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (12--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BM_LOAD_TAC `x0:num->int16` 16 16 BM_ADDR_A THEN
    BM_LOAD_TAC `x1:num->int16` 16 16 BM_ADDR_B THEN
    BM_LOAD_TAC `x2:num->int16` 16 16 BM_ADDR_B2 THEN
    BM_LOAD_TAC `y0:num->int16` 16 16 BM_ADDR_A THEN
    BM_LOAD_TAC `y1:num->int16` 16 16 BM_ADDR_B THEN
    BM_LOAD_TAC `y2:num->int16` 16 16 BM_ADDR_B2 THEN
    BM_LOAD_TAC `y0t:num->int16` 8 8 BM_ADDR_C THEN
    BM_LOAD_TAC `y1t:num->int16` 8 8 BM_ADDR_D THEN
    BM_LOAD_TAC `y2t:num->int16` 8 8 BM_ADDR_D2 THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 4 t))
     [`read(memory :> bytes256(word_add srcA (word(32 * i)))) s0`;
    `read(memory :> bytes256(word_add srcA (word(32 * i + 512)))) s0`;
    `read(memory :> bytes256(word_add srcA (word(32 * i + 1024)))) s0`;
    `read(memory :> bytes256(word_add srcB (word(32 * i)))) s0`;
    `read(memory :> bytes256(word_add srcB (word(32 * i + 512)))) s0`;
    `read(memory :> bytes256(word_add srcB (word(32 * i + 1024)))) s0`] THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 3 t))
     [`read(memory :> bytes128(word_add srcBt (word(16 * i)))) s0`;
    `read(memory :> bytes128(word_add srcBt (word(16 * i + 256)))) s0`;
    `read(memory :> bytes128(word_add srcBt (word(16 * i + 512)))) s0`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[montred_neon]) (1--51) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes256 a) s51 = x`)
            (concl th) && free_in `dst:int64` (concl th)))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
    DISCH_TAC THEN
    MAP_EVERY (fun c ->
    FIRST_ASSUM(MP_TAC o SPEC (subst [mk_small_numeral c,`c:num`]
                                   `16 * i + c`) o
                check (fun th -> is_forall(concl th) &&
                                 free_in `abs:int->int` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC]) (0--15) THEN
    X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j < 8 * i` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?k. k < 8 /\ j = 8 * i + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `j - 8 * i` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `j:num`)) THEN
    UNDISCH_TAC `k < 8` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BM_ADDR_E; BM_ADDR_F] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MONTRED_NEON_SCALAR]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BM3_CONG_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word_add srcBt (word (16 * i))) (word 256))
                   (word_add srcBt (word 512)):int64) = 0)`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[WORD_RULE
     `word_sub (word_add (word_add a x) y) (word_add a z):int64 =
    word_sub (word_add x y) z`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 16 ==> 16 * i + 256 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word 256)) (word 256):int64 =
    word_add a (word 512)`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST]);;

let WORD_ZX_ZX_64_128 = prove
 (WORD_ZX_ZX_64_128_STMT,
  CONV_TAC WORD_BLAST);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (sp:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc sp returnaddress)
        (APPEND
          (ENUMERATEL 16
            (\i. f_ev_loop srcA srcB srcBt dst pc sp returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc sp returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(TRY_CONV NORMALIZE_ALIGNED_WORD_CONV)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_DREG_TAC "d8_init" `D8` THEN
  ENSURES_PRESERVED_DREG_TAC "d9_init" `D9` THEN
  ENSURES_PRESERVED_DREG_TAC "d10_init" `D10` THEN
  ENSURES_PRESERVED_DREG_TAC "d11_init" `D11` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16`
   `pc + mlkem768_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem768_polyvec_basemul_acc_montgomery_cached_loop1_exit`
    `\i s. read X2 s = word_add srcA (word(32 * i)) /\
           read X1 s = word_add srcB (word(32 * i)) /\
           read X0 s = word_add (word_add srcBt (word(16 * i))) (word 256) /\
           read X5 s = word_add dst (word(32 * i)) /\
           read X7 s = word_add srcBt (word 512) /\
           read SP s = stackpointer /\
           read(memory :> bytes64 stackpointer) s = x19_init /\
           read(memory :> bytes64(word_add stackpointer (word 8))) s =
           returnaddress /\
           read(memory :> bytes64(word_add stackpointer (word 16))) s =
           d8_init /\
           read(memory :> bytes64(word_add stackpointer (word 24))) s =
           d9_init /\
           read(memory :> bytes64(word_add stackpointer (word 32))) s =
           d10_init /\
           read(memory :> bytes64(word_add stackpointer (word 40))) s =
           d11_init` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The check for overlap and the setup ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`dst:int64`; `srcBt:int64`; `768`] BASEMUL_ALIAS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN ARITH_TAC;
                    DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--8) THEN
    FIRST_X_ASSUM(fun th -> if is_cond(concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[th]) else failwith "") THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (9--11) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (12--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--51) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (52--53) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word_add srcBt (word (16 * i))) (word 272))
                     (word_add srcBt (word 512)):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add (word_add a x) y) (word_add a z):int64 =
        word_sub (word_add x y) z`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 ==> 16 * i + 272 < 18446744073709551616`] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                  ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Restoring the registers and the return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O3_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_ZX_ZX_64_128] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
