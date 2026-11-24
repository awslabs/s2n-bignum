(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm_avx512/sha3_keccak_f1600_avx512_spec.ml";;

let KECCAK_AVX512_SPLIT_LOW = prove
 (KECCAK_AVX512_SPLIT_LOW_STMT,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  CONV_TAC WORD_BLAST);;

let SHA3_KECCAK_F1600_AVX512_FULL = time prove
 (SHA3_KECCAK_F1600_AVX512_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
       (APPEND
         (ENUMERATEL 6
           (\i. APPEND (APPEND (APPEND (f_ev_r4 rc a pc i) (f_ev_r3 rc a pc i))
                               (f_ev_r2 rc a pc i))
                       (f_ev_r1 rc a pc i)))
         (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `LENGTH(A:int64 list) = 25` THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x95` `pc + 0xc7b`
   `\i s. read RDI s = a /\
           read RSI s = word_add rc (word(32 * i)) /\
           read RAX s = word_add rc (word 192) /\
           wordlist_from_memory(rc,24) s = round_constants /\
           [word_subword (read YMM0 s) (0,64);
            word_subword (read YMM1 s) (0,64);
            word_subword (read YMM2 s) (0,64);
            word_subword (read YMM3 s) (0,64);
            word_subword (read YMM4 s) (0,64);
            word_subword (read YMM5 s) (0,64);
            word_subword (read YMM6 s) (0,64);
            word_subword (read YMM7 s) (0,64);
            word_subword (read YMM8 s) (0,64);
            word_subword (read YMM9 s) (0,64);
            word_subword (read YMM10 s) (0,64);
            word_subword (read YMM11 s) (0,64);
            word_subword (read YMM12 s) (0,64);
            word_subword (read YMM13 s) (0,64);
            word_subword (read YMM14 s) (0,64);
            word_subword (read YMM15 s) (0,64);
            word_subword (read YMM16 s) (0,64);
            word_subword (read YMM17 s) (0,64);
            word_subword (read YMM18 s) (0,64);
            word_subword (read YMM19 s) (0,64);
            word_subword (read YMM20 s) (0,64);
            word_subword (read YMM21 s) (0,64);
            word_subword (read YMM22 s) (0,64);
            word_subword (read YMM23 s) (0,64);
            word_subword (read YMM24 s) (0,64)] =
           keccak_avx512_lanes keccak_avx512_layout0 (keccak (4 * i) A)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    MP_TAC(ISPEC `A:int64 list` LENGTH_EQ_25) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[MULT_CLAUSES; keccak; keccak_avx512_lanes;
                keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC; WORD_ADD_0] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC ONCE_DEPTH_CONV [ENUMERATEL_ADD1] THEN
    CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x364`
     (keccak_avx512_assertion `keccak_avx512_layout1` `4 * i + 1`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 1 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x634`
     (keccak_avx512_assertion `keccak_avx512_layout2` `4 * i + 2`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 2 105; ALL_TAC] THEN
    KECCAK_AVX512_EVENTS_REASSOC_TAC THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x904`
     (keccak_avx512_assertion `keccak_avx512_layout3` `4 * i + 3`) THEN
    CONJ_TAC THENL [KECCAK_AVX512_FULL_ROUND_TAC 3 105; ALL_TAC] THEN
    KECCAK_AVX512_FULL_ROUND_TAC 4 136;

    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY (fun k ->
      ABBREV_TAC(mk_eq(mk_var("z"^string_of_int k,`:int64`),
        list_mk_comb(`EL:num->int64 list->int64`,
          [mk_small_numeral k; `keccak 24 A`])))) (0--24) THEN
    REWRITE_TAC[keccak_avx512_lanes; keccak_avx512_layout0; MAP] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV EL_CONV) THEN
    REWRITE_TAC[round_constants;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`;
      WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(a,25) s:int64 list`] THEN
    REWRITE_TAC[CONS_11; GSYM CONJ_ASSOC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    KECCAK_AVX512_HIGHS_TAC THEN
    X86_STEPS_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC (1--26) THEN
    ENSURES_FINAL_STATE_TAC THEN
    EVENTS_SPLIT_TAC
     (ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST)]);;

let SHA3_KECCAK_F1600_AVX512_CORRECT = prove
 (SHA3_KECCAK_F1600_AVX512_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  X_CHOOSE_TAC `f:int64->int64->num->(uarch_event)list`
   SHA3_KECCAK_F1600_AVX512_FULL THEN
  MATCH_MP_TAC(ISPEC `read events:x86state->(uarch_event)list`
                ENSURES_ANY_INITIAL) THEN
  X_GEN_TAC `e:(uarch_event)list` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `rc:int64`; `A:int64 list`; `pc:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_MONO_ALL) THEN
  SIMP_TAC[]);;

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT = prove
 (SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT_STMT,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK_F1600_AVX512_CORRECT));;

let SHA3_KECCAK_F1600_AVX512_SUBROUTINE_CORRECT = prove
 (SHA3_KECCAK_F1600_AVX512_SUBROUTINE_CORRECT_STMT,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV
     SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_CORRECT)));;

let SHA3_KECCAK_F1600_AVX512_SAFE = time prove
 (SHA3_KECCAK_F1600_AVX512_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rc:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rc a pc)
             (APPEND (ENUMERATEL 6 (\i. f_ev_loop rc a pc i))
                     (f_ev_prol rc a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `rc:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + 0x95` `pc + 0xc7b`
   `\i s. read RDI s = a /\
          read RSI s = word_add rc (word(32 * i)) /\
          read RAX s = word_add rc (word 192)` THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false SHA3_KECCAK_F1600_AVX512_TMC_EXEC
      (1--26) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    KECCAK_AVX512_SAFE_SIM_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC 451 THEN
    ASM_SIMP_TAC[KECCAK_AVX512_BRANCH] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[KECCAK_AVX512_RSI]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false SHA3_KECCAK_F1600_AVX512_TMC_EXEC
      (1--26) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE = time prove
 (SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE_STMT,
  X86_ADD_RETURN_NOSTACK_TAC SHA3_KECCAK_F1600_AVX512_TMC_EXEC
   SHA3_KECCAK_F1600_AVX512_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let SHA3_KECCAK_F1600_AVX512_SUBROUTINE_SAFE = time prove
 (SHA3_KECCAK_F1600_AVX512_SUBROUTINE_SAFE_STMT,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE));;
