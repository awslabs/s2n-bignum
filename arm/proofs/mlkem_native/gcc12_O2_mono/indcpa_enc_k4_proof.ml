(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/indcpa_enc_k4_spec.ml";;


let KPKE_ENCRYPT_K4_RESULT = prove
 (KPKE_ENCRYPT_K4_RESULT_STMT,
  let inv_tac ui k =
    W(fun (_,w) ->
      let pinv = find_term (fun t -> match t with
        Comb(Const("mlkem_ntt_inv",_),_) -> true | _ -> false) w in
      SUBGOAL_THEN
       (mk_comb(mk_comb(`(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`,
                        pinv),`ring_carrier mlkem_rq`)) ASSUME_TAC THENL
       [MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
        REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [rand pinv; ui; `&169:int`; k] MLKEM_NTT_INV_CONG_MUL) THEN
      ANTS_TAC THENL
       [CONV_TAC(DEPTH_CONV BETA_CONV) THEN
        ASM_SIMP_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
        DISCH_TAC])
  and digit_tac =
    AP_THM_TAC THEN AP_TERM_TAC THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("num_of_int",_),
             Comb(Comb(Const("rem",_),
                  Comb(Comb(Const("mlkem_compress",_),_),_)),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) MLKEM_COMPRESS_DIGIT t)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VAL_EQ_NUM_OF_INT_IVAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MLKEM_COEFF_POS THEN
      REPEAT(MATCH_MP_TAC RING_ADD THEN
             REWRITE_TAC[MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ]) THEN
      MATCH_MP_TAC MLKEM_NTT_INV_IN_RQ THEN
      REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM];
      ALL_TAC]
  and parity_tac =
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
  MP_TAC(SPECL [`4`; `2`; `2`; `11`; `5`; `ek:byte list`; `m:byte list`;
                `r:byte list`] KPKE_ENCRYPT_FIPS) THEN
  REWRITE_TAC[ARITH_RULE `384 * 4 = 1536`] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; MLKEM_ENCODE_LENGTH] THEN
  REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; ARITH_RULE `2 * 4 = 8`;
              ARITH_RULE `(11 * 1024) DIV 8 = 1408`] THEN
  W(fun (_,w) ->
    let encs = find_terms (fun t -> match strip_comb t with
       (Const("mlkem_encode",_),[_;_;_]) -> true | _ -> false) w in
    MAP_EVERY (fun enc ->
      MP_TAC(PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE
              (mk_comb(`num_of_bytelist`,enc)))) encs) THEN
  REPEAT(ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV THENC DIVIDES_CONV);
    DISCH_THEN SUBST1_TAC]) THEN
  BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  digit_tac THENL
   [MP_TAC(SPECL [`256`; `4`; `i:num`] EXISTS_DIV_MOD_LT) THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 * 4 = 1024`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `n:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DIV_MOD_ADD_LT] THEN
    SUBGOAL_THEN
     `!n'. n' < 256
           ==> (ival((U0:num->int16)(256 * j + n')) ==
                &169 * ring_sum mlkem_zq {j' | j' < 4}
                        (\j'. fips203_multiply_ntts
                               (mlkem_sample_ntt
                                 (APPEND (mlkem_slice 1536 32 ek)
                                         [word j; word j']))
                               (mlkem_ntt
                                 (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                               n')) (mod &3329)`
    ASSUME_TAC THENL
     [parity_tac THENL
       [MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. ival((MC:num->int16)(128 * j' + p))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p))`; `p:num`]
         BASEMUL4_ROW_EVEN);
        MP_TAC(SPECL
         [`\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j'. mlkem_sample_ntt
                 (APPEND (mlkem_slice 1536 32 ek) [word j; word j'])`;
          `\j' n. ival((YH:num->int16)(256 * j' + n))`;
          `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
          `ival((U0:num->int16)(256 * j + 2 * p + 1))`; `p:num`]
         BASEMUL4_ROW_ODD)] THEN
      row_tac;
      ALL_TAC] THEN
    W(fun (_,w) ->
      let t = find_term (fun t -> match t with
        Comb(Const("ival",_),Comb(Comb(Const("word_add",_),_),_)) -> true
        | _ -> false) w in
      MP_TAC(PART_MATCH (lhand o rand) IVAL_WORD_ADD_BOUNDED t)) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `abs(ival((U1:num->int16)(256 * j + n))) <= &26624 /\
                    abs(ival((E1:num->int16)(256 * j + n))) <= &2`
      MP_TAC THENL [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      DISCH_THEN SUBST1_TAC] THEN
    inv_tac `\n'. ival((U0:num->int16)(256 * j + n'))` `n:num` THEN
    ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ] THEN
    REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(a:int == c) (mod q) /\ (b == d) (mod q)
      ==> (a + b == c + d) (mod q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n'. ival((U0:num->int16)(256 * j + n'))) n` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n'. n' < 256
         ==> (ival((V0:num->int16) n') ==
              &169 * ring_sum mlkem_zq {j' | j' < 4}
                      (\j'. fips203_multiply_ntts
                             (\n. mlkem_decode 12 ek (256 * j' + n))
                             (mlkem_ntt
                               (mlkem_cbd 2 (mlkem_prf 2 r (word j'))))
                             n')) (mod &3329)`
  ASSUME_TAC THENL
   [parity_tac THEN
    (SUBGOAL_THEN
      `!j' x. j' < 4 /\ x < 256
              ==> (ival((TT:num->int16)(256 * j' + x)) ==
                   mlkem_decode 12 ek (256 * j' + x)) (mod &3329)`
     ASSUME_TAC THENL
      [REPEAT STRIP_TAC THEN MATCH_MP_TAC TT_DECODE_CONG THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       UNDISCH_TAC `j' < 4` THEN UNDISCH_TAC `x < 256` THEN ARITH_TAC;
       ALL_TAC])
    THENL
     [MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. ival((MC:num->int16)(128 * j' + p))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p))`; `p:num`] BASEMUL4_ROW_EVEN);
      MP_TAC(SPECL
       [`\j' n. mlkem_decode 12 ek (256 * j' + n)`;
        `\j' n. ival((TT:num->int16)(256 * j' + n))`;
        `\j' n. ival((YH:num->int16)(256 * j' + n))`;
        `\j'. mlkem_ntt (mlkem_cbd 2 (mlkem_prf 2 r (word j')))`;
        `ival((V0:num->int16)(2 * p + 1))`; `p:num`] BASEMUL4_ROW_ODD)] THEN
    row_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN `(num_of_bytelist m DIV 2 EXP i) MOD 2 < 2` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival((MU:num->int16) i) =
    &((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MU_IVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ival((V1:num->int16) i)) <= &26624 /\
                abs(ival((E2:num->int16) i)) <= &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add ((V1:num->int16) i) ((E2:num->int16) i)) =
    ival(V1 i) + ival(E2 i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o fst o chop_list 2) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ival(word_add (word_add ((V1:num->int16) i) ((E2:num->int16) i))
                  ((MU:num->int16) i)) =
    ival(word_add (V1 i) (E2 i)) + ival(MU i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_WORD_ADD_BOUNDED THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `abs(ival((V1:num->int16) i)) <= &26624` THEN
    UNDISCH_TAC `abs(ival((E2:num->int16) i)) <= &2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  inv_tac `\n. ival((V0:num->int16) n)` `i:num` THEN
  ASM_SIMP_TAC[MLKEM_RQ_COEFF_ADD; MLKEM_CBD_IN_RQ; MLKEM_POLY_IN_RQ;
               RING_ADD] THEN
  ASM_REWRITE_TAC[COEFF_MLKEM_POLY; MLKEM_DECODE_1] THEN
  ASM_SIMP_TAC[MLKEM_DECOMPRESS_1] THEN
  REWRITE_TAC[MLKEM_ZQ_ADD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ADD3_REM_ALT THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INT_CONG_MONT_CANCEL THEN
    EXISTS_TAC `inverse_ntt (\n. ival((V0:num->int16) n)) i` THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
    MP_TAC(ARITH_RULE
     `(3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2 <= 1665`) THEN
    ARITH_TAC]);;

let EN4_ALIGNED_16_32 = prove
 (EN4_ALIGNED_16_32_STMT,
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

let EN4_BUFFER_ADDRESS = prove
 (EN4_BUFFER_ADDRESS_STMT,
  REWRITE_TAC[EN4_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let EN4_D11_ARITH = prove
 (EN4_D11_ARITH_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4096 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4096 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4096 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(4294967296 + v * 5284526080) - q * 8589934592` THEN
  ASM_ARITH_TAC);;

let EN4_WORD_SX_SMALL_64 = prove
 (EN4_WORD_SX_SMALL_64_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let EN4_D11_FIELD = prove
 (EN4_D11_FIELD_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EN4_WORD_SX_SMALL_64; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 18446744073709551616`;
    ARITH_RULE `y < 3329
                ==> 4294967296 + y * 5284526080 < 18446744073709551616`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[EN4_D11_ARITH]);;

let EN4_VAL_JOIN_11X8 = prove
 (EN4_VAL_JOIN_11X8_STMT,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:11 word`; `u1:11 word`; `u2:11 word`; `u3:11 word`;
    `u4:11 word`; `u5:11 word`; `u6:11 word`; `u7:11 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:11 word->num`,
                     mk_var("u"^string_of_int k,`:11 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

let EN4_D11_IDX = prove
 (EN4_D11_IDX_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `word_zx (word_zx (word n:int64):int32):int64 = word n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `n < 256 ==> n < 4294967296 /\ n < 18446744073709551616`];
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

let EN4_D11_TEST = prove
 (EN4_D11_TEST_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 32 ==> 8 * i + 8 < 18446744073709551616 /\
               8 * i + 8 < 4294967296 /\
               (8 * i + 8) + 8 < 4294967296 /\
               (8 * i + 8) + 8 < 18446744073709551616`] THEN
  UNDISCH_TAC `i < 32` THEN ARITH_TAC);;

let EN4_D11 = prove
 (EN4_D11_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (a:int64) (j:num) (pc:num) (stackpointer:int64).
      APPEND (f_ev_epil r a j pc stackpointer)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop r a j pc stackpointer i))
               (f_ev_prol r a j pc stackpointer))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `r:int64`; `a:int64`; `x:num->int16`;
                       `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst EN4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_indcpa_enc_loop9`
   `pc + mlkem1024_indcpa_enc_loop9_exit` EN4_D11_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC;
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o check (is_imp o concl));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for eight coefficients and eleven bytes ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun jt ->
    FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE
       [ARITH_RULE `!j n. 512 * j + 2 * n = 2 * (256 * j + n)`])])
   (butlast en4_d11_indices) THEN
  EN4_D11_BODY_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP EN4_D11_TEST (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + 1) + 8 = (8 * i + 8) + 8`] THEN
    WORD_SMALL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EN4_D11_SPLIT_TAC THEN MAP_EVERY EN4_D11_PACK_TAC (0--10) THEN
  REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`word_add r (word(11 * i)):int64`; `11`;
                mk_comb(`val:88 word->num`,en4_d11_join); `s117:armstate`]
               READ_MEMORY_BYTES_OF_BYTES8) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_CLAUSES;
                WORD_ADD_0] THEN
    ASM_REWRITE_TAC[EN4_WORD_SUBWORD_BYTE] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPEC en4_d11_join VAL_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  SIMP_TAC[MOD_LT] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EN4_VAL_JOIN_11X8] THEN
  MAP_EVERY (fun jt ->
    MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) EN4_D11_FIELD) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check
       (can (term_match []
              `!m. m < 256 ==> val((x:num->int16) m) < 3329`) o concl)) THEN
      UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC]) (butlast en4_d11_indices) THEN
  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
  REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let EN4_D5_ARITH = prove
 (EN4_D5_ARITH_STMT,
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let EN4_WORD_SX_SMALL_32 = prove
 (EN4_WORD_SX_SMALL_32_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let EN4_D5_FIELD = prove
 (EN4_D5_FIELD_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EN4_WORD_SX_SMALL_32; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
               ARITH_RULE `y < 3329 ==> y < 18446744073709551616`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 134217728 * 32`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[EN4_D5_ARITH]);;

let EN4_BYTES_OF_NUM_5 = prove
 (EN4_BYTES_OF_NUM_5_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(n DIV 4294967296) MOD 256 = n DIV 4294967296`
   SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP 40` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 65536`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`n DIV 16777216`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV; ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let EN4_VAL_JOIN_5X8 = prove
 (EN4_VAL_JOIN_5X8_STMT,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> MP_TAC(ISPEC t VAL_BOUND))
   [`u0:5 word`; `u1:5 word`; `u2:5 word`; `u3:5 word`;
    `u4:5 word`; `u5:5 word`; `u6:5 word`; `u7:5 word`] THEN
  REWRITE_TAC[VAL_WORD_JOIN] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY (fun k ->
    SPEC_TAC(mk_comb(`val:5 word->num`,mk_var("u"^string_of_int k,`:5 word`)),
             mk_var("n"^string_of_int k,`:num`))) (0--7) THEN
  REPEAT STRIP_TAC THEN REPEAT MOD_LT_ASM_TAC THEN ARITH_TAC);;

let EN4_D5_TEST = prove
 (EN4_D5_TEST_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 32 ==> 8 * i < 18446744073709551616 /\ 8 * i < 4294967296 /\
               8 * i + 8 < 4294967296 /\
               8 * i + 8 < 18446744073709551616`] THEN
  UNDISCH_TAC `i < 32` THEN ARITH_TAC);;

let EN4_D5 = prove
 (EN4_D5_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (a:int64) (pc:num) (stackpointer:int64).
      APPEND (f_ev_epil r a pc stackpointer)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop r a pc stackpointer i))
               (f_ev_prol r a pc stackpointer))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`;
                       `stackpointer:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst EN4_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem1024_indcpa_enc_loop11`
   `pc + mlkem1024_indcpa_enc_loop11_exit`
   `\i s. read SP s = stackpointer /\
          read X19 s = word_add r (word(5 * i)) /\
          read X9 s = word(8 * i) /\
          read X8 s = word_add stackpointer (word 19168) /\
          read X26 s = a /\ read X7 s = word 1290176 /\
          read X6 s = word 67108864 /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,5 * i)) s =
               nsum {j | j < 8 * i}
                (\j. ((64 * val(x j) + 3329) DIV 6658) MOD 32 *
                     2 EXP (5 * j)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0;
                NSUM_CLAUSES_NUMSEG_LT; READ_MEMORY_BYTES_TRIVIAL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o check (is_imp o concl));
      DISCHARGE_SAFETY_PROPERTY_TAC]] THEN

  (*** The loop body, for eight coefficients and five bytes ***)

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun jt ->
    FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC])
   en4_d5_indices THEN
  EN4_D5_BODY_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP EN4_D5_TEST (ASSUME `i < 32`)]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN WORD_SMALL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

  (*** The new bytes as parts of the join of the 5-bit fields ***)

  MAP_EVERY EN4_D5_PACK_TAC (0--4) THEN
  REWRITE_TAC[ARITH_RULE
   `5 * (i + 1) = ((((5 * i + 1) + 1) + 1) + 1) + 1`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE `(5 * i + 1) + 1 = 5 * i + 2`;
              ARITH_RULE `(5 * i + 2) + 1 = 5 * i + 3`;
              ARITH_RULE `(5 * i + 3) + 1 = 5 * i + 4`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INST_TYPE [`:40`,`:M`; `:8`,`:N`] VAL_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(SPEC (mk_comb(`val:40 word->num`,en4_d5_join)) EN4_BYTES_OF_NUM_5) THEN
  MP_TAC(ISPEC en4_d5_join VAL_BOUND) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th)) THEN
  REWRITE_TAC[EN4_VAL_JOIN_5X8] THEN

  (*** The compression of each coefficient ***)

  MAP_EVERY (fun jt ->
    MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) EN4_D5_FIELD) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check
       (can (term_match []
              `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o concl)) THEN
      UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC]) en4_d5_indices THEN

  (*** The new values in the number for the output ***)

  REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD] THEN
  REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let EN4_NSUM_SHIFT_EXP = prove
 (EN4_NSUM_SHIFT_EXP_STMT,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM NSUM_LMUL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let EN4_COMPRESS_DU_STEP = prove
 (EN4_COMPRESS_DU_STEP_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `352 * (k + 1) = 352 * k + 352`;
              ARITH_RULE `256 * (k + 1) = 256 * k + 256`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; NSUM_LT_ADD] THEN
  REWRITE_TAC[EN4_NSUM_SHIFT_EXP] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 352 * k = 11 * 256 * k`; MULT_ASSOC]);;

let EN4_COMPRESS_DU_JOIN = prove
 (EN4_COMPRESS_DU_JOIN_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`r:int64`; `s:armstate`; `g:num->num`; `3`] EN4_COMPRESS_DU_STEP)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`r:int64`; `s:armstate`; `g:num->num`; `2`] EN4_COMPRESS_DU_STEP)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`r:int64`; `s:armstate`; `g:num->num`; `1`] EN4_COMPRESS_DU_STEP)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  EN4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN4_CASE_TAC 3840; EN4_CASE_TAC 3856]);;

let MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  EN4_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [EN4_SAFE_CASE_TAC 3840; EN4_SAFE_CASE_TAC 3856]);;
