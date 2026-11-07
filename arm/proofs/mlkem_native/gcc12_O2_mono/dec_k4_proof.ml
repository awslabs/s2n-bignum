(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/dec_k4_spec.ml";;


let KPKE_DECRYPT_K4_RESULT = prove
 (KPKE_DECRYPT_K4_RESULT_STMT,
  let parity_tac =
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `128`; `n':num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 128 = 256`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `b:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
      MATCH_MP(ARITH_RULE `b < 2 ==> b = 0 \/ b = 1`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    (SUBGOAL_THEN `2 * p < 256 /\ 2 * p + 1 < 256` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `p < 128` THEN ARITH_TAC; ALL_TAC])
and row_tac =
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; INT_CONG_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mlkem1024] THEN
  REWRITE_TAC[KPKE_DECRYPT_FIPS] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  W(fun (_,w) ->
    let enc = find_term (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
            (mk_comb(`num_of_bytelist`,enc)))) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[MULT_CLAUSES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let wt = find_term (fun t -> match t with
      Comb(Comb(Comb(Const("ring_sub",_),_),_),_) -> true | _ -> false) w in
    SUBGOAL_THEN
     (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                      wt),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[MLKEM_POLY_IN_RQ];
      ALL_TAC]) THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("num_of_int",_),
           Comb(Comb(Const("rem",_),
                Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC MLKEM_COEFF_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_SUB; MLKEM_POLY_IN_RQ] THEN
  REWRITE_TAC[MLKEM_ZQ; INT_REM_EQ] THEN
  ABBREV_TAC `fv = (num_of_bytelist (mlkem_slice 1408 160 ct) DIV
                    2 EXP (5 * i)) MOD 2 EXP 5` THEN
  SUBGOAL_THEN `(3329 * fv + 16) DIV 32 < 3329` ASSUME_TAC THENL
   [SUBGOAL_THEN `fv < 32` MP_TAC THENL
     [EXPAND_TAC "fv" THEN
      REWRITE_TAC[ARITH_RULE `32 = 2 EXP 5`; MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word((3329 * fv + 16) DIV 32):int16) =
                &((3329 * fv + 16) DIV 32)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_SMALL THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((WI:num->int16) i)) <= &26624` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  W(fun (_,w) ->
    let t = find_term (fun t -> match t with
      Comb(Const("ival",_),Comb(Comb(Const("word_sub",_),_),_)) -> true
      | _ -> false) w in
    MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_SUB_BOUNDED t)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(3329 * fv + 16) DIV 32 < 3329` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
    UNDISCH_TAC `abs(ival((WI:num->int16) i)) <= &26624` THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  SIMP_TAC[MLKEM_DECODE_SMALL; ARITH_RULE `5 < 12`] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&((3329 * fv + 16) DIV 32) rem &3329 = &((3329 * fv + 16) DIV 32)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INT_REM_LT THEN REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(b:int == d) (mod q) ==> (a - b == a - d) (mod q)`) THEN
  SUBGOAL_THEN
   `!j' n. j' < 4 /\ n < 256
           ==> (ival((UH:num->int16)(256 * j' + n)) ==
                mlkem_ntt (mlkem_poly
                  (\j''. mlkem_decompress 11
                          (mlkem_decode 11 ct (256 * j' + j'')))) n)
               (mod &3329)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC `\n. (UD:num->int16)(256 * j' + n)` THEN
    REWRITE_TAC[MLKEM_POLY_IN_RQ] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[] THEN
    X_GEN_TAC `n':num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `256 * j' + n' < 1024` ASSUME_TAC THENL
     [UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `n' < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_SMALL; ARITH_RULE `11 < 12`;
                 MLKEM_DECOMPRESS_NUM; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN
    ABBREV_TAC `fu = (num_of_bytelist ct DIV 2 EXP (11 * (256 * j' + n'))) MOD
                     2048` THEN
    SUBGOAL_THEN `fu < 2048` MP_TAC THENL
     [EXPAND_TAC "fu" THEN REWRITE_TAC[MOD_LT_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV;
      DISCH_TAC] THEN
    SUBGOAL_THEN `ival(word((3329 * fu + 1024) DIV 2048):int16) =
                  &((3329 * fu + 1024) DIV 2048)` SUBST1_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_SMALL THEN UNDISCH_TAC `fu < 2048` THEN ARITH_TAC;
      REWRITE_TAC[INT_CONG_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((WP:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 dk (256 * j' + n))
                             (mlkem_ntt (mlkem_poly
                               (\j''. mlkem_decompress 11
                                       (mlkem_decode 11 ct (256 * j' + j'')))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((SS:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 dk (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 dk (256 * j' + n)`;
        `\j' n. ival((SS:num->int16)(256 * j' + n))`;
        `\j' n. ival((UH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_poly
                (\j''. mlkem_decompress 11
                        (mlkem_decode 11 ct (256 * j' + j''))))`;
        `ival((WP:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let pinv = find_term (fun t -> match t with
      Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
    MP_TAC(ISPECL [rand pinv; `\n. ival((WP:num->int16) n)`; `&169:int`;
                   `i:num`] MLKEM_NTT_INV_CONG_MUL)) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
  EXISTS_TAC `inverse_ntt (\n. ival((WP:num->int16) n)) i` THEN
  ASM_SIMP_TAC[]);;

let KD4_D11_BYTES = prove
 (KD4_D11_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let KD4_D11_HALF = prove
 (KD4_D11_HALF_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:armstate`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;

let KD4_D11D_LANE = prove
 (KD4_D11D_LANE_STMT,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:11 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:11 word)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `v MOD 65536 = v /\ v MOD 4294967296 = v`
   (fun th -> REWRITE_TAC[th])
  THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `v < 2048 ==> v * 3329 < 4294967296 /\ v * 3329 + 1024 < 4294967296`] THEN
  SUBGOAL_THEN `(v * 3329 + 1024) DIV 2048 < 65536 /\
                (3329 * v + 1024) DIV 2048 < 65536`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let KD4_D11D_FIELD = prove
 (KD4_D11D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;

let KD4_LOOP_TEST = prove
 (KD4_LOOP_TEST_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[WORD_RULE `word_add a x = word_add a y <=> x:int64 = y`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `m * i + m < 2 EXP 64 /\ m * n < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [ASM_REWRITE_TAC[] THEN
    TRANS_TAC LET_TRANS `m * n` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `m * i + m = m * (i + 1)`] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m * i + m = m * (i + 1)`] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let KD4_D11 = prove
 (KD4_D11_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (r:int64) (pc:num).
      APPEND (f_ev_epil a r pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a r pc i)) (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `r:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst KD4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop2`
   `pc + mlkem1024_dec_loop2_exit` KD4_D11_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> is_forall(concl th) &&
                         free_in `bytes16` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for eleven bytes and eight coefficients ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun j ->
    MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
               mk_small_numeral j] KD4_D11_BYTES)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) (1--10) THEN
  MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] KD4_D11_HALF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--50) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o KD4_D11D_LANE_RULE o
                       CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th)) THEN
  ARM_STEPS_TAC KD4_EXEC (51--52) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONV_RULE NUM_REDUCE_CONV
   (MP (SPECL [`a:int64`; `11`; `32`; `i:num`] KD4_LOOP_TEST)
       (CONJ (EQT_ELIM(NUM_REDUCE_CONV `~(11 = 0)`))
             (CONJ (ASSUME `i < 32`) (EQT_ELIM(NUM_REDUCE_CONV
                                         `11 * 32 < 2 EXP 64`)))))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `j < 8 * (i + 1) <=>
    j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
    j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
    j = 8 * i + 7`] THEN
  REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
              ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
              ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
              ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
              ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
              ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
              ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
              ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL (map KD4_D11D_FIELD_TAC (0--7)));;

let KD4_D5_BYTES = prove
 (KD4_D5_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `160`; `n:num`; `5 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

let KD4_D5D_LANE = prove
 (KD4_D5D_LANE_STMT,
  GEN_TAC THEN REWRITE_TAC[WORD_SHL_ZERO] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_MUL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:5 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:5 word)`,`v:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let KD4_D5D_FIELD = prove
 (KD4_D5D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 5 5 = 5`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 5 * k + 5 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `32 = 2 EXP 5`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 5 * k = 5 * (8 * i + k)`]);;

let KD4_D5 = prove
 (KD4_D5_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (r:int64) (pc:num).
      APPEND (f_ev_epil a r pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a r pc i)) (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `r:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst KD4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop3`
   `pc + mlkem1024_dec_loop3_exit` KD4_D5_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> is_forall(concl th) &&
                         free_in `bytes16` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for five bytes and eight coefficients ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun j ->
    MP_TAC(REWRITE_RULE[ADD_CLAUSES]
     (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
               mk_small_numeral j] KD4_D5_BYTES))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--4) THEN
  ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KD4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[]) (1--39) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
           concl)) THEN
  DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o KD4_D5D_LANE_RULE o
                       CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th)) THEN
  ARM_STEPS_TAC KD4_EXEC (40--41) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONV_RULE NUM_REDUCE_CONV
   (MP (SPECL [`r:int64`; `16`; `32`; `i:num`] KD4_LOOP_TEST)
       (CONJ (EQT_ELIM(NUM_REDUCE_CONV `~(16 = 0)`))
             (CONJ (ASSUME `i < 32`) (EQT_ELIM(NUM_REDUCE_CONV
                                         `16 * 32 < 2 EXP 64`)))))]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  REWRITE_TAC[ARITH_RULE
   `j < 8 * (i + 1) <=>
    j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
    j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
    j = 8 * i + 7`] THEN
  REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
              ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
              ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
              ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
              ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
              ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
              ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
              ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL (map KD4_D5D_FIELD_TAC (0--7)));;

let KD4_DU_SPLIT = prove
 (KD4_DU_SPLIT_STMT,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE;
              ARITH_RULE `2816 * j = 8 * 352 * j`;
              ARITH_RULE `2816 = 8 * 352`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let KD4_DU_FIELD = prove
 (KD4_DU_FIELD_STMT,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIV_MOD] THEN
  REWRITE_TAC[GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `i < 256 ==> MIN 2816 (11 * i + 11) = 11 * i + 11`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_MOD; DIV_DIV]);;

let KD4_DEC_A = KD4_DEC_LEMMA 23008;;

let KD4_DEC_U = KD4_DEC_LEMMA 22992;;

let KPKE_ENCRYPT_LENGTH_1024 = prove
 (KPKE_ENCRYPT_LENGTH_1024_STMT,
  REWRITE_TAC[mlkem1024; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let KPKE_DECRYPT_LENGTH_1024 = prove
 (KPKE_DECRYPT_LENGTH_1024_STMT,
  REWRITE_TAC[mlkem1024; KPKE_DECRYPT_LENGTH]);;

let KD4_CHECK = prove
 (KD4_CHECK_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem1024; mlkem_decaps_check] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[mlkem_h] THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ; LENGTH_SHA3_256]);;

let KD4_ALIGNED_16_32 = prove
 (KD4_ALIGNED_16_32_STMT,
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

let KD4_BUFFER_ADDRESS = prove
 (KD4_BUFFER_ADDRESS_STMT,
  REWRITE_TAC[KD4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KD4_TEST = prove
 (KD4_TEST_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
              WORD_RULE `word_sub (word_add a x) (word_add a y):int64 =
                         word_sub x y`] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `b + 5664 < 2 EXP 64 /\ ((b + 4096) + 16 * i) + 16 < 2 EXP 64`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let KD4_KP_ADDR2 = prove
 (KD4_KP_ADDR2_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  KD4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KD4_CASE_TAC 23008; KD4_CASE_TAC 22992]);;

let KD4_DEC_SAFE_A = prove
 (KD4_DEC_SAFE_A_STMT, KD4_DEC_SAFE_TAC);;

let KD4_DEC_SAFE_U = prove
 (KD4_DEC_SAFE_U_STMT, KD4_DEC_SAFE_TAC);;

let KD4_DEC_SAFE = prove
 (KD4_DEC_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(UNDISCH(SPEC_ALL KD4_DEC_SAFE_A)) THEN
  DISCH_THEN(X_CHOOSE_TAC
   `fa:int64->int64->int64->num->int64->(uarch_event)list`) THEN
  MP_TAC(UNDISCH(SPEC_ALL KD4_DEC_SAFE_U)) THEN
  DISCH_THEN(X_CHOOSE_TAC
   `fu:int64->int64->int64->num->int64->(uarch_event)list`) THEN
  EXISTS_TAC
   `\(sk:int64) (c:int64) (mf:int64) (pc:num) (stackpointer:int64)
      (b:num).
       if b = 23008 then fa sk c mf pc stackpointer
       else fu sk c mf pc stackpointer:(uarch_event)list` THEN
  REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    DISJ_CASES_THEN (fun eq -> SUBST1_TAC eq THEN
                               MP_TAC(REWRITE_RULE[eq] (CONJUNCT2 th)))
     (CONJUNCT1 th)) THEN
  REWRITE_TAC[ARITH_EQ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let KD4_KBAR_ADDR = prove
 (KD4_KBAR_ADDR_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[KD4_KP_ADDR2] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[ARITH_RULE
   `(a + b) + (i + 1) + 18446744073709551615 =
    1 * 18446744073709551616 + (a + b + i)`; MOD_MULT_ADD]);;

let MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_DEC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  KD4_SAFE_INTRO_TAC THEN
  ASM_CASES_TAC
   `num_of_bytelist(hh:byte list) = num_of_bytelist(sha3_256 ekk)` THEN
  ASM_REWRITE_TAC[] THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `98` `pc + mlkem1024_dec_loop7`
    `pc + mlkem1024_dec_loop7_exit`
     KD4_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC; KD4_SAFE_PART1_TAC; KD4_SAFE_BODY_TAC;
      ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_dec_loop8`
       `pc + mlkem1024_dec_loop8_exit`
       KD4_SAFE_CMOV_INV THEN
      REPEAT CONJ_TAC THENL
       [ARITH_TAC; KD4_SAFE_EXIT_A_TAC; KD4_SAFE_CMOV_BODY_TAC;
        KD4_SAFE_EXIT_B_TAC]];
    KD4_SAFE_BAD_TAC]);;
