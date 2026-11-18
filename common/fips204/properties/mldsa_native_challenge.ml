(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tools for the proofs of mldsa44_poly_challenge,                *)
(* mldsa65_poly_challenge and mldsa87_poly_challenge (see                    *)
(* common/mldsa_native_challenge.ml).                                        *)
(*                                                                           *)
(* The code reads the bytes of the SHAKE256 output one by one from a buffer  *)
(* of one block, squeezing the next block when the buffer is used up. The    *)
(* proofs treat this as one loop over the bytes from position 8 on, whose    *)
(* head is the read of the next byte from the buffer, or the squeeze of the  *)
(* next block if the byte starts one: the loop head depends on the           *)
(* iteration, as in MLD_CHALLENGE_WHILE_THM, a form of the theorem behind    *)
(* ENSURES_WHILE_UP2_TAC with the PC of the head a function of the           *)
(* iteration, and MLD_CHALLENGE_WHILE_TAC is the corresponding form of       *)
(* ENSURES_EVENTS_WHILE_UP2_TAC.                                             *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_hash.ml";;
needs "common/fips204/properties/mldsa_native_prefix.ml";;
needs "common/mldsa_native_challenge.ml";;

(* ------------------------------------------------------------------------- *)
(* The steps of the specification: after byte n, by whether it is accepted;  *)
(* the number of coefficients set is at most tau and does not decrease, and  *)
(* if it reaches tau, it does so after mld_poly_challenge_bytes bytes, the   *)
(* last of which is accepted.                                                *)
(* ------------------------------------------------------------------------- *)

let MLD_POLY_CHALLENGE_STEP_ADD1 = prove
 (`!tau (s:num->byte) n.
     mld_poly_challenge_step tau s (n + 1) =
     if mld_poly_challenge_accept tau s n
     then FST(mld_poly_challenge_step tau s n) + 1,
          (\t. if t = val(s(8 + n))
               then mld_poly_challenge_sign s
                     (FST(mld_poly_challenge_step tau s n))
               else if t = 256 - tau + FST(mld_poly_challenge_step tau s n)
               then SND(mld_poly_challenge_step tau s n) (val(s(8 + n)))
               else SND(mld_poly_challenge_step tau s n) t)
     else mld_poly_challenge_step tau s n`,
  REWRITE_TAC[GSYM ADD1; mld_poly_challenge_step; mld_poly_challenge_next;
              mld_poly_challenge_accept] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLD_POLY_CHALLENGE_STEP_LE = prove
 (`!tau (s:num->byte) n. FST(mld_poly_challenge_step tau s n) <= tau`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 mld_poly_challenge_step; LE_0] THEN
  REWRITE_TAC[ADD1; MLD_POLY_CHALLENGE_STEP_ADD1] THEN
  REWRITE_TAC[mld_poly_challenge_accept] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let MLD_POLY_CHALLENGE_BYTES = prove
 (`!tau (s:num->byte).
     (?n. FST(mld_poly_challenge_step tau s n) = tau)
     ==> FST(mld_poly_challenge_step tau s (mld_poly_challenge_bytes tau s)) =
         tau /\
         (!n. n < mld_poly_challenge_bytes tau s
              ==> FST(mld_poly_challenge_step tau s n) < tau)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[mld_poly_challenge_bytes] THEN
  MP_TAC(BETA_RULE(ISPEC `\n. FST(mld_poly_challenge_step tau (s:num->byte) n)
                              = tau` MINIMAL)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`tau:num`; `s:num->byte`; `n:num`]
    MLD_POLY_CHALLENGE_STEP_LE) THEN
  ARITH_TAC);;

let MLD_POLY_CHALLENGE_BYTES_POS = prove
 (`!tau (s:num->byte).
     (?n. FST(mld_poly_challenge_step tau s n) = tau) /\ ~(tau = 0)
     ==> ~(mld_poly_challenge_bytes tau s = 0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o CONJUNCT1 o MATCH_MP MLD_POLY_CHALLENGE_BYTES) ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(q ==> ~p) ==> p ==> ~q`) THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[mld_poly_challenge_step]);;

let MLD_POLY_CHALLENGE_BYTES_NEXT = prove
 (`!tau (s:num->byte) n.
     (?n. FST(mld_poly_challenge_step tau s n) = tau) /\
     n < mld_poly_challenge_bytes tau s
     ==> (n + 1 < mld_poly_challenge_bytes tau s <=>
          ~(mld_poly_challenge_accept tau s n /\
            FST(mld_poly_challenge_step tau s n) + 1 = tau))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (STRIP_ASSUME_TAC o MATCH_MP MLD_POLY_CHALLENGE_BYTES) ASSUME_TAC) THEN
  ABBREV_TAC `N = mld_poly_challenge_bytes tau (s:num->byte)` THEN
  SUBGOAL_THEN `FST(mld_poly_challenge_step tau (s:num->byte) n) < tau`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `n + 1 < N <=> FST(mld_poly_challenge_step tau (s:num->byte) (n + 1)) < tau`
  SUBST1_TAC THENL
   [EQ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `n + 1 = N` THENL
     [ASM_REWRITE_TAC[LT_REFL];
      UNDISCH_TAC `n < N` THEN UNDISCH_TAC `~(n + 1 = N)` THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MLD_POLY_CHALLENGE_STEP_ADD1] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `FST(mld_poly_challenge_step tau (s:num->byte) n) < tau` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The bytes of a buffer holding a list given as a function.                 *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_BYTELIST_DIGIT = prove
 (`!(f:num->byte) n t.
     t < n
     ==> (num_of_bytelist(list_of_seq f n) DIV 2 EXP (8 * t)) MOD 256 =
         val(f t)`,
  GEN_TAC THEN REWRITE_TAC[EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  INDUCT_TAC THEN REWRITE_TAC[LT] THEN
  REWRITE_TAC[list_of_seq; MLD_PREFIX_NUM_OF_BYTELIST_APPEND;
              LENGTH_LIST_OF_SEQ; num_of_bytelist; MULT_CLAUSES;
              ADD_CLAUSES; EXP_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) n` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  ABBREV_TAC `A = num_of_bytelist(list_of_seq (f:num->byte) n)` THEN
  DISCH_TAC THEN X_GEN_TAC `t:num` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ISPEC `(f:num->byte) n` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    SUBGOAL_THEN `256 EXP n = 256 EXP t * 256 * 256 EXP (n - (t + 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 EXP); GSYM EXP_ADD; ADD1] THEN
      AP_TERM_TAC THEN UNDISCH_TAC `t < n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[MOD_MULT_ADD] THEN FIRST_X_ASSUM(MP_TAC o SPEC `t:num`) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Squeezing a block of 136 bytes from the position 136: the bytes are those *)
(* of the stream of the first state after the blocks before, and the state   *)
(* is permuted once more.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_SQUEEZE_ADD = prove
 (`!m n (S:1600 word).
     keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let MLD_CHALLENGE_SQUEEZE_BYTE = prove
 (`!(S:1600 word) m j.
     mld_keccak_squeeze_byte 136 (keccak_squeeze m S) 136 j =
     mld_keccak_squeeze_byte 136 S 136 (136 * m + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MLD_CHALLENGE_SQUEEZE_ADD] THEN
  REWRITE_TAC[ARITH_RULE `136 + 136 * m + j = 136 * m + 136 + j`] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; ADD_SYM]);;

let MLD_CHALLENGE_SQUEEZE_STATE = prove
 (`!S:1600 word.
     mld_keccak_squeeze_state 136 S 136 136 = keccak_squeeze 1 S,136`,
  REWRITE_TAC[mld_keccak_squeeze_state] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_CHALLENGE_SQUEEZE_BYTE_FUN = prove
 (`!(S:1600 word) m.
     mld_keccak_squeeze_byte 136 (keccak_squeeze m S) 136 =
     \j. mld_keccak_squeeze_byte 136 S 136 (136 * m + j)`,
  REWRITE_TAC[FUN_EQ_THM; MLD_CHALLENGE_SQUEEZE_BYTE]);;

(*** The state after absorbing fewer than 136 bytes and finalizing ***)

let MLD_CHALLENGE_STATE = prove
 (`!n M. n < 136
         ==> mld_keccak_finalize 136 31
               (FST(mld_keccak_absorb 136 (word 0) 0 n M)) n =
             mld_shake256_state n M`,
  SIMP_TAC[mld_shake256_state; MLD_KECCAK_ABSORB_SND; ADD_CLAUSES; MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* The buffer of 136 bytes is aligned to 32 bytes within the stack frame of  *)
(* 448 bytes at stackpointer + 256, so that its address depends on whether   *)
(* the stack pointer is a multiple of 32 or just of 16.                      *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_BUFFER_ADDRESS = prove
 (`!sptr:int64.
        aligned 16 sptr
        ==> word_and (word_add sptr (word 351)) (word 18446744073709551584) =
            word_add sptr (word(if aligned 32 sptr then 320 else 336))`,
  SUBGOAL_THEN
   `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
    (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
      MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
             ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
             ARITH_RULE `x < 32 ==> x < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16 ==> x MOD 16 < 2 EXP 64`;
             MOD_LT_EQ; ARITH_EQ; ARITH_RULE `x MOD 32 < 32`;
             ARITH_RULE `x MOD 16 < 18446744073709551616`;
             ARITH_RULE `x MOD 32 < 18446744073709551616`];
    GEN_TAC THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]);;

(* ------------------------------------------------------------------------- *)
(* The position of byte n from position 8 on in the buffer: the code keeps   *)
(* p = (7 + n) MOD 136 + 1 in 1..136 in W0 and block (7 + n) DIV 136 in the  *)
(* buffer, and squeezes the next block before reading when p = 136.          *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_POS_SUC = prove
 (`!q. q MOD 136 < 135
       ==> (q + 1) MOD 136 = q MOD 136 + 1 /\ (q + 1) DIV 136 = q DIV 136`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`q:num`; `136`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q DIV 136`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `q MOD 136 + 1`] THEN
  ASM_ARITH_TAC);;

let MLD_CHALLENGE_POS_WRAP = prove
 (`!q. q MOD 136 = 135
       ==> (q + 1) MOD 136 = 0 /\ (q + 1) DIV 136 = q DIV 136 + 1`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`q:num`; `136`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q DIV 136 + 1`;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0`] THEN
  ASM_ARITH_TAC);;

let MLD_CHALLENGE_POS_ZERO = prove
 (`!q. (q + 1) MOD 136 = 0 <=> q MOD 136 = 135`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; SIMP_TAC[MLD_CHALLENGE_POS_WRAP]] THEN
  MP_TAC(SPECL [`q:num`; `136`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `q MOD 136 = 135` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `q MOD 136 < 135`
   (fun th -> SIMP_TAC[MLD_CHALLENGE_POS_SUC; th])
  THENL [ASM_ARITH_TAC; ARITH_TAC]);;

let MLD_CHALLENGE_POS_SPLIT = prove
 (`!q. 136 * q DIV 136 + q MOD 136 + 1 = q + 1`,
  GEN_TAC THEN MP_TAC(SPECL [`q:num`; `136`] DIVISION) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Values of words: the comparisons of the byte j (or the position) with i   *)
(* in 32-bit registers as CMP leaves them for B.LS, B.HI and B.NE, and the   *)
(* zero extensions of small values.                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_CMP = prove
 (`!x y:int32.
     (&(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x) /\
     (val(word_sub x y) = 0 <=> val x = val y)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
    MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN
    MP_TAC(ISPEC `y:int32` VAL_BOUND) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD;
                GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_SUB] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    INT_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; VAL_EQ]]);;

let MLD_CHALLENGE_CMP_VAL = prove
 (`!x y:int32 m.
     val y = m
     ==> (&(val x) - &m:int = &(val(word_sub x y)) <=> m <= val x) /\
         (val(word_sub x y) = 0 <=> val x = m)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MLD_CHALLENGE_CMP]);;

let MLD_CHALLENGE_VAL_ZX3 = prove
 (`!b:byte. val(word_zx(word_zx(word_zx b:int32):int64):int32) = val b`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32;
                           DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\
                val(b:byte) MOD 18446744073709551616 = val b`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let MLD_CHALLENGE_VAL_ZX_WORD = prove
 (`!m. m < 2 EXP 32 ==> val(word_zx(word m:int64):int32) = m`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m /\ m MOD 4294967296 = m`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let MLD_CHALLENGE_ZX_ZX_WORD = prove
 (`!m. m < 2 EXP 32 ==> word_zx(word_zx(word m:int64):int32):int64 = word m`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m /\ m MOD 4294967296 = m`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let MLD_CHALLENGE_ZX_BYTE = prove
 (`!b:byte. word_zx(word_zx b:int32):int64 = word(val b)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\
                val(b:byte) MOD 18446744073709551616 = val b`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let MLD_CHALLENGE_UXTW_TAC idx =
  MP_TAC(SPEC idx VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

let MLD_CHALLENGE_EXIT_TEST_TAC =
  W(fun (asl,w) ->
    let pat = `val(word_add (word m) (word k):int64) = 0` in
    let tms = setify(flat(map (fun (_,th) ->
      find_terms (fun t -> can (term_match [] pat) t &&
                           is_numeral(rand(rand(rand(lhand t)))))
                 (concl th)) asl)) in
    MAP_EVERY (fun t ->
      let th = INSTANTIATE (term_match [] pat t)
                (SPECL [`m:num`; `k:num`] VAL_WORD_ADD_COMPLEMENT_EQ_0) in
      MP_TAC th THEN ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun eth -> RULE_ASSUM_TAC(REWRITE_RULE[eth]) THEN
                              RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV
                                NUM_REDUCE_CONV)))]) tms);;

(* ------------------------------------------------------------------------- *)
(* Rewriting some assumptions only: MLD_CHALLENGE_FIX_TAC p ths rewrites     *)
(* those whose conclusion satisfies p with ths, for example the value of one *)
(* register (mld_challenge_is_read_reg) or the 32-bit values in memory       *)
(* (mld_challenge_is_bytes32), and MLD_CHALLENGE_ZX_ZX_TAC t replaces the    *)
(* zero extensions of word t to 32 and back to 64 bits by word t, for a      *)
(* small t, in the assumptions.                                              *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_FIX_TAC pred ths =
  RULE_ASSUM_TAC(fun th -> if pred(concl th) then REWRITE_RULE ths th else th);;

let MLD_CHALLENGE_ZX_ZX_TAC tm =
  MP_TAC(SPEC tm MLD_CHALLENGE_ZX_ZX_WORD) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
    (mk_eq(mk_comb(`word_zx:int32->int64`,
                   mk_comb(`word_zx:int64->int32`,
                           mk_comb(`word:num->int64`,tm))),
           mk_comb(`word:num->int64`,tm)))]);;

(* ------------------------------------------------------------------------- *)
(* The coefficients across the two stores c[i] = c[j] and c[j] = +-1 of an   *)
(* accepted byte j: before them, MLD_CHALLENGE_EXCLUDE_TAC i j adds the      *)
(* coefficients other than i and j, which the stores do not change, and      *)
(* afterwards MLD_CHALLENGE_POLY_TAC i proves the coefficients of the new    *)
(* polynomial, from the store to j, the store to i if i is not j, and the    *)
(* others. The byte is j and i is the term for the index i.                  *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_EXCLUDE_TAC i j =
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes32` (concl th) then
      let t = `t:num` in
      let ant = list_mk_conj
                 [`t < 256`; mk_neg(mk_eq(t,i)); mk_neg(mk_eq(t,j))] in
      ASSUME_TAC th THEN
      ASSUME_TAC(GEN t (DISCH ant (MP (SPEC t th) (CONJUNCT1(ASSUME ant)))))
    else NO_TAC);;

let MLD_CHALLENGE_POLY_TAC i =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `t:num = j` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC (mk_eq(`t:num`,i)) THENL
   [ASM_REWRITE_TAC[] THEN
    (FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[MLD_PREFIX_ZX_ZX] THEN
     NO_TAC) ORELSE
    (SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC);
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The end of an iteration of the loop over the bytes. The proof abbreviates *)
(* the values that depend on n (whose definitions mention val, which         *)
(* SIMPLE_ARITH_TAC ignores), and MLD_CHALLENGE_UNABBREV_TAC prs puts back   *)
(* the abbreviations v = t in prs that are there before the events are       *)
(* matched with the template. MLD_CHALLENGE_DISCHARGE_TAC tac then selects   *)
(* the path of the template by the case assumptions, as PATH_DISCHARGE_TAC   *)
(* does, with the safety property of the events so far split out of the one  *)
(* for e2 (which must stay free, see MLD_PREFIX_DISCHARGE_TAC), instantiates *)
(* the function of the path or checks the events against it if another case  *)
(* has instantiated it, and proves that the accesses are in bounds, after    *)
(* tac.                                                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_CHALLENGE_UNABBREV_TAC prs =
  MAP_EVERY (fun (t,v) ->
    TRY(FIRST_X_ASSUM(fun th ->
      if concl th = mk_eq(t,v) then SUBST_ALL_TAC(SYM th) else NO_TAC))) prs;;
