(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridge between the Keccak-f[1600] of common/fips202/fips202.ml and the    *)
(* lane-list formulation of common/fips202/properties/keccak_spec.ml, which  *)
(* the Keccak assembly proofs in {arm,x86}/proofs use. The lemmas below      *)
(* prove KECCAK_F1600_BRIDGE with the lane tables of fips202_eval.ml, as     *)
(* common/fips202/properties/keccak_f1600.ml does for the proofs; that file  *)
(* needs the memory model of base.ml, which the tests do not load.           *)
(* ========================================================================= *)

needs "tests/mlkem/fips202_eval.ml";;
needs "common/fips202/properties/keccak_spec.ml";;

(* keccak_spec.ml makes ~~, &&, || and ^^ the operations of words; restore   *)
(* their usual meaning for the files that follow.                            *)

remove_interface "~~";; unparse_as_prefix "~~";;
remove_interface "&&";; unparse_as_infix "&&";;
remove_interface "||";; unparse_as_infix "||";;
remove_interface "^^";; unparse_as_infix "^^";;

(* ------------------------------------------------------------------------- *)
(* The round constants agree, and each round agrees lane by lane.            *)
(* ------------------------------------------------------------------------- *)

let KECCAK_ROUND_CONSTANTS_TABLE = prove
 (`!i. i < 24 ==> EL i round_constants = keccak_round_constant i`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC KECCAK_ROUND_CONSTANTS THEN
  REWRITE_TAC[round_constants] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let KECCAK_RND_ROUND = prove
 (`!i l. LENGTH l = 25
         ==> keccak_agree (keccak_rnd i (keccak_table l))
                (keccak_table (keccak_round (keccak_round_constant i) l))`,
  let vs = mk_list(keccak_table_vars,`:int64`) in
  let rhs_lane j =
    let tm = list_mk_comb(`keccak_table`,
      [mk_comb(mk_comb(`keccak_round`,`keccak_round_constant i`),vs);
       mk_small_numeral(j mod 5); mk_small_numeral(j / 5)]) in
    (REWRITE_CONV[keccak_table] THENC NUM_REDUCE_CONV THENC
     REWRITE_CONV[keccak_round] THENC TOP_DEPTH_CONV let_CONV THENC
     DEPTH_CONV EL_CONV THENC REWRITE_CONV[]) tm
  and lhs_lane j =
    MP (INST [`keccak_round_constant i`,`rc:int64`] (el j KECCAK_RND_TABLE))
       (REFL `keccak_round_constant i`) in
  let lanes = map (fun j -> TRANS (lhs_lane j) (SYM(rhs_lane j))) (0--24) in
  let ath = INST [mk_comb(`keccak_rnd i`,mk_comb(`keccak_table`,vs)),
                  `a:num->num->int64`;
                  mk_comb(`keccak_table`,
                   mk_comb(mk_comb(`keccak_round`,
                                   `keccak_round_constant i`),vs)),
                  `b:num->num->int64`] KECCAK_AGREE_EXPAND in
  let th = EQ_MP (SYM ath) (end_itlist CONJ lanes) in
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [LENGTH_EQ_25] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(INST (map2 (fun j v -> (mk_comb(mk_comb(`EL:num->int64 list->int64`,
                                   mk_small_numeral j),`l:int64 list`),v))
                    (0--24) keccak_table_vars) (GEN `i:num` th)) THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

let KECCAK_ROUNDS_BRIDGE = prove
 (`!n l. LENGTH l = 25 /\ n <= 24
         ==> keccak_agree (keccak_rounds n (keccak_table l))
                          (keccak_table (keccak n l))`,
  INDUCT_TAC THEN REWRITE_TAC[keccak_rounds; keccak] THENL
   [REWRITE_TAC[keccak_agree]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD1; keccak] THEN
  MATCH_MP_TAC KECCAK_AGREE_TRANS THEN
  EXISTS_TAC `keccak_rnd n (keccak_table (keccak n l))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC KECCAK_AGREE_RND THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[KECCAK_ROUND_CONSTANTS_TABLE;
                 ARITH_RULE `SUC n <= 24 ==> n < 24`] THEN
    MATCH_MP_TAC KECCAK_RND_ROUND THEN ASM_SIMP_TAC[LENGTH_KECCAK]]);;

let KECCAK_F1600_BRIDGE = prove
 (`!l. LENGTH l = 25
       ==> keccak_f1600 (keccak_state (keccak_table l)) =
           keccak_state (keccak_table (keccak 24 l))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`keccak_state (keccak_table l)`; `keccak_table l`]
                KECCAK_F1600_AGREE) THEN
  REWRITE_TAC[keccak_agree; KECCAK_LANES_STATE] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC KECCAK_STATE_AGREE THEN
  MATCH_MP_TAC KECCAK_ROUNDS_BRIDGE THEN ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Faster evaluation of keccak_f1600 on concrete states, through the lane    *)
(* list form, evaluating each let-bound lane once.                           *)
(* ------------------------------------------------------------------------- *)

let rec LETS_EVAL_CONV ev tm =
  if is_let tm then
    let bs,_ = dest_let tm in
    let rec args n = if n = 0 then ALL_CONV
                     else RAND_CONV ev THENC RATOR_CONV(args(n - 1)) in
    let th1 = args (length bs) tm in
    let th2 = CONV_RULE(RAND_CONV let_CONV) th1 in
    TRANS th2 (LETS_EVAL_CONV ev (rand(concl th2)))
  else ev tm;;

let KECCAK_ROUND_EVAL_CONV =
  let ev = TRY_CONV EL_CONV THENC WORD_REDUCE_CONV in
  REWR_CONV keccak_round THENC LETS_EVAL_CONV ev THENC
  LIST_CONV WORD_REDUCE_CONV;;

let KECCAK_LIST_CONV =
  let [pth0;pth1] = CONJUNCTS keccak in
  fun tm ->
    match tm with
      Comb(Comb(Const("keccak",_),n),l) ->
        let rec iter k th =
          if k = Num.int_of_num(dest_numeral n) then th else
          let tm' = mk_comb(mk_comb(`keccak`,mk_small_numeral(k + 1)),l) in
          let eqn =
            SYM(NUM_ADD_CONV(mk_binary "+" (mk_small_numeral k,`1`))) in
          let th1 = (RATOR_CONV(RAND_CONV(K eqn)) THENC REWR_CONV pth1) tm' in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV th))) th1 in
          let th3 = CONV_RULE(RAND_CONV(LAND_CONV
                      (RAND_CONV(REWR_CONV round_constants) THENC EL_CONV)))
                     th2 in
          iter (k + 1) (CONV_RULE(RAND_CONV KECCAK_ROUND_EVAL_CONV) th3) in
        iter 0 (INST [l,`l:int64 list`] (SPEC_ALL pth0))
    | _ -> failwith "KECCAK_LIST_CONV";;

let KECCAK_F1600_FAST_CONV tm =
  match tm with
    Comb(Const("keccak_f1600",_),s) ->
      let laneconv = REWRITE_CONV[keccak_lanes] THENC NUM_REDUCE_CONV THENC
                     WORD_REDUCE_CONV in
      let lths = map (fun j -> laneconv(list_mk_comb(mk_comb(`keccak_lanes`,s),
                        [mk_small_numeral(j mod 5); mk_small_numeral(j / 5)])))
                     (0--24) in
      let l0 = mk_list(map (rand o concl) lths,`:int64`) in
      let rhs = map (INST (zip (dest_list l0) keccak_table_vars))
                    KECCAK_TABLE_LANES in
      let conjs = map2 (fun th1 th2 -> TRANS th1 (SYM th2)) lths rhs in
      let ath = INST [mk_comb(`keccak_lanes`,s),`a:num->num->int64`;
                      mk_comb(`keccak_table`,l0),`b:num->num->int64`]
                     KECCAK_AGREE_EXPAND in
      let th0 = EQ_MP (SYM ath) (end_itlist CONJ conjs) in
      let ths = TRANS (SYM(SPEC s KECCAK_STATE_LANES))
                      (MATCH_MP KECCAK_STATE_AGREE th0) in
      let lenth = LENGTH_CONV(mk_comb(`LENGTH:int64 list->num`,l0)) in
      let thb = MP (SPEC l0 KECCAK_F1600_BRIDGE) lenth in
      let th1 = TRANS (AP_TERM `keccak_f1600` ths) thb in
      let th2 =
        CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV KECCAK_LIST_CONV))) th1 in
      let lf = rand(rand(rand(concl th2))) in
      let fths = map (INST (zip (dest_list lf) keccak_table_vars))
                     KECCAK_TABLE_LANES in
      CONV_RULE(RAND_CONV(REWRITE_CONV[keccak_state] THENC
                          ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
                          NUM_REDUCE_CONV THENC PURE_REWRITE_CONV fths THENC
                          WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) th2
  | _ -> failwith "KECCAK_F1600_FAST_CONV";;

keccak_f1600_conv := KECCAK_F1600_FAST_CONV;;
