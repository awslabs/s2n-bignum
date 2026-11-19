(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_2_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The byte at offset k of an array of l bytes with value n, and the prefix  *)
(* of k + 1 bytes of two such arrays as the prefix of k bytes and a byte.    *)
(* ------------------------------------------------------------------------- *)

let CTMEMCMP_BYTE = prove
 (`!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ k < l
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 8)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[READ_BYTES_DIV; ARITH_RULE `256 = 2 EXP (8 * 1)`;
              READ_BYTES_MOD; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `MIN (l - k) 1 = 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let CTMEMCMP_BOUND = prove
 (`!a len s:armstate. read (memory :> bytes(a,len)) s < 2 EXP (8 * len)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let CTMEMCMP_BYTE_EQ = prove
 (`!p q. p < 256 /\ q < 256 ==> (p = q <=> (word p:byte) = word q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let CTMEMCMP_MOD_STEP = prove
 (`!n m k. n MOD 2 EXP (8 * (k + 1)) = m MOD 2 EXP (8 * (k + 1)) <=>
           n MOD 2 EXP (8 * k) = m MOD 2 EXP (8 * k) /\
           (n DIV 2 EXP (8 * k)) MOD 2 EXP 8 =
           (m DIV 2 EXP (8 * k)) MOD 2 EXP 8`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8 * (k + 1) = 8 * k + 8`; EXP_ADD] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEXICOGRAPHIC_EQ o lhand o snd) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

(*** The counter, a 32-bit register, as a 64-bit number ***)

let CTMEMCMP_ZX_UP = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 4294967296 ==> n < 18446744073709551616`]);;

let CTMEMCMP_ZX_DOWN = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int64):int32 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 4294967296 ==> n < 18446744073709551616`]);;

(*** The rewrites for the counter of iteration i, given i + 1 < 2^32 ***)

let CTMEMCMP_COUNTER_RULES =
  let h1 = ASSUME `i < 2 EXP 32` and h2 = ASSUME `i + 1 < 2 EXP 32` in
  [MP (SPEC `i:num` CTMEMCMP_ZX_DOWN) h1; GSYM WORD_ADD;
   MP (SPEC `i + 1` CTMEMCMP_ZX_UP) h2; MP (SPEC `i + 1` CTMEMCMP_ZX_DOWN) h2];;

let MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (b:int64) (len:num) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a b len pc returnaddress)
        (APPEND
          (ENUMERATEL len (\i. f_ev_loop a b len pc returnaddress i))
          (f_ev_prol a b len pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `b:int64`; `len:num`; `n:num`; `m:num`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; fst MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The invariant is at the first instruction of the loop body, at 0x34
       bytes from the start of the function. The test of the loop is the
       three instructions before it, which are also run before the first
       iteration, and the last iteration ends at the loop exit. ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + 23952`
   `pc + mld_ct_memcmp_2_loop1_exit`
   `\i s. read X0 s = a /\ read X1 s = b /\ read X2 s = word len /\
          read X30 s = returnaddress /\
          read X6 s = word i /\ read X7 s = word i /\
          read (memory :> bytes(a,len)) s = n /\
          read (memory :> bytes(b,len)) s = m /\
          word_zx(word_zx(read X3 s):byte):int64 = read X3 s /\
          word_zx(word_zx(read X5 s):byte):int64 = read X5 s /\
          (read X3 s = word 0 <=> n MOD 2 EXP (8 * i) = m MOD 2 EXP (8 * i))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN
    SUBGOAL_THEN `len < 2 EXP 64` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; LE_0; VAL_WORD_0; WORD_ZX_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_1] THEN
    SUBGOAL_THEN `~(len = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `0 < len` THEN ARITH_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, up to the next test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `x3:int64` `read X3` THEN
    GHOST_INTRO_TAC `x5:int64` `read X5` THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_ASSUM(fun th ->
      if lhand(concl th) = `read (memory :> bytes(a,len)) s0`
      then ASSUME_TAC(MP (SPECL [`a:int64`; `len:num`; `i:num`; `n:num`;
                                 `s0:armstate`] CTMEMCMP_BYTE)
                         (CONJ th (ASSUME `i < len`)))
      else NO_TAC) THEN
    FIRST_ASSUM(fun th ->
      if lhand(concl th) = `read (memory :> bytes(b,len)) s0`
      then ASSUME_TAC(MP (SPECL [`b:int64`; `len:num`; `i:num`; `m:num`;
                                 `s0:armstate`] CTMEMCMP_BYTE)
                         (CONJ th (ASSUME `i < len`)))
      else NO_TAC) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `i < 2 EXP 32 /\ i + 1 < 2 EXP 32 /\
      i + 1 < 18446744073709551616 /\ len < 18446744073709551616`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i < len`; `len < 2 EXP 32`] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [(*** The branch back is taken if and only if i + 1 < len ***)

      REWRITE_TAC CTMEMCMP_COUNTER_RULES THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN
      REWRITE_TAC[ARITH_RULE
       `i + 1 <= len /\ ~(len = i + 1) <=> i + 1 < len`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];

      REWRITE_TAC CTMEMCMP_COUNTER_RULES;
      REWRITE_TAC CTMEMCMP_COUNTER_RULES;

      (*** The accumulators remain bytes: their OR and their XOR ***)

      UNDISCH_TAC `word_zx(word_zx(x3:int64):byte):int64 = x3` THEN
      SPEC_TAC(`word ((n DIV 2 EXP (8 * i)) MOD 256):byte`,`da:byte`) THEN
      SPEC_TAC(`word ((m DIV 2 EXP (8 * i)) MOD 256):byte`,`db:byte`) THEN
      SPEC_TAC(`x3:int64`,`x3:int64`) THEN BITBLAST_TAC;

      UNDISCH_TAC `word_zx(word_zx(x5:int64):byte):int64 = x5` THEN
      SPEC_TAC(`word ((n DIV 2 EXP (8 * i)) MOD 256):byte`,`da:byte`) THEN
      SPEC_TAC(`word ((m DIV 2 EXP (8 * i)) MOD 256):byte`,`db:byte`) THEN
      SPEC_TAC(`x5:int64`,`x5:int64`) THEN BITBLAST_TAC;

      (*** The OR is zero if and only if the prefixes are equal ***)

      REWRITE_TAC[CTMEMCMP_MOD_STEP] THEN
      FIRST_X_ASSUM(fun th ->
        if is_iff(concl th) && lhand(concl th) = `x3:int64 = word 0`
        then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
      MP_TAC(SPECL [`(n DIV 2 EXP (8 * i)) MOD 256`;
                    `(m DIV 2 EXP (8 * i)) MOD 256`] CTMEMCMP_BYTE_EQ) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
        DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      UNDISCH_TAC `word_zx(word_zx(x3:int64):byte):int64 = x3` THEN
      SPEC_TAC(`word ((n DIV 2 EXP (8 * i)) MOD 256):byte`,`da:byte`) THEN
      SPEC_TAC(`word ((m DIV 2 EXP (8 * i)) MOD 256):byte`,`db:byte`) THEN
      SPEC_TAC(`x3:int64`,`x3:int64`) THEN BITBLAST_TAC;

      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit: the result from the two accumulators ***)

    GHOST_INTRO_TAC `x3:int64` `read X3` THEN
    GHOST_INTRO_TAC `x5:int64` `read X5` THEN
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`a:int64`; `len:num`; `s0:armstate`] CTMEMCMP_BOUND) THEN
    MP_TAC(SPECL [`b:int64`; `len:num`; `s0:armstate`] CTMEMCMP_BOUND) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    SUBGOAL_THEN `x3:int64 = word 0 <=> (n:num) = m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `x3:int64 = word 0` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC];
      SUBGOAL_THEN `~(x3:int64 = word 0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC]] THEN
    UNDISCH_TAC `word_zx(word_zx(x5:int64):byte):int64 = x5` THEN
    UNDISCH_TAC `word_zx(word_zx(x3:int64):byte):int64 = x3` THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC(`x5:int64`,`x5:int64`) THEN SPEC_TAC(`x3:int64`,`x3:int64`) THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]);;

(*** The correctness and the safety theorems follow from the combined one ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  X_CHOOSE_TAC `f:int64->int64->num->num->int64->(uarch_event)list`
   MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `b:int64`; `len:num`; `n:num`;
    `m:num`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLDSA_NATIVE_CT_MEMCMP_2_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `n:num` `read (memory :> bytes(a,len))` THEN
  GHOST_INTRO_TAC `m:num` `read (memory :> bytes(b,len))` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `b:int64`; `len:num`; `n:num`;
    `m:num`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
