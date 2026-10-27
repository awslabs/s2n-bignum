(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridge between the Keccak-f[1600] of common/fips202.ml and the lane-list  *)
(* formulation used by the Keccak assembly proofs in {arm,x86}/proofs (from  *)
(* {arm,x86}/proofs/utils/keccak_spec.ml, whose definitions are reproduced   *)
(* verbatim below, so that loading both gives benign redefinitions).         *)
(* ========================================================================= *)

needs "tests/mlkem/fips202_eval.ml";;

parse_as_prefix "~~";;
override_interface("~~",`word_not:N word->N word`);;
parse_as_infix("&&",(13,"right"));;
override_interface("&&",`word_and:N word->N word->N word`);;
parse_as_infix("||",(13,"right"));;
override_interface("^^",`word_xor:N word->N word->N word`);;
parse_as_infix("^^",(13,"right"));;
override_interface("||",`word_or:N word->N word->N word`);;

let round_constants = define
 `round_constants:int64 list =
   [word 0x0000000000000001;
    word 0x0000000000008082;
    word 0x800000000000808a;
    word 0x8000000080008000;
    word 0x000000000000808b;
    word 0x0000000080000001;
    word 0x8000000080008081;
    word 0x8000000000008009;
    word 0x000000000000008a;
    word 0x0000000000000088;
    word 0x0000000080008009;
    word 0x000000008000000a;
    word 0x000000008000808b;
    word 0x800000000000008b;
    word 0x8000000000008089;
    word 0x8000000000008003;
    word 0x8000000000008002;
    word 0x8000000000000080;
    word 0x000000000000800a;
    word 0x800000008000000a;
    word 0x8000000080008081;
    word 0x8000000000008080;
    word 0x0000000080000001;
    word 0x8000000080008008]`;;

let keccak_round = define
 `(keccak_round:int64 -> int64 list->int64 list) RCi Alist =
  let A00 = EL  0 Alist
  and A10 = EL  1 Alist
  and A20 = EL  2 Alist
  and A30 = EL  3 Alist
  and A40 = EL  4 Alist
  and A01 = EL  5 Alist
  and A11 = EL  6 Alist
  and A21 = EL  7 Alist
  and A31 = EL  8 Alist
  and A41 = EL  9 Alist
  and A02 = EL 10 Alist
  and A12 = EL 11 Alist
  and A22 = EL 12 Alist
  and A32 = EL 13 Alist
  and A42 = EL 14 Alist
  and A03 = EL 15 Alist
  and A13 = EL 16 Alist
  and A23 = EL 17 Alist
  and A33 = EL 18 Alist
  and A43 = EL 19 Alist
  and A04 = EL 20 Alist
  and A14 = EL 21 Alist
  and A24 = EL 22 Alist
  and A34 = EL 23 Alist
  and A44 = EL 24 Alist in
  let C0 = A00 ^^ A01 ^^ A02 ^^ A03 ^^ A04
  and C1 = A10 ^^ A11 ^^ A12 ^^ A13 ^^ A14
  and C2 = A20 ^^ A21 ^^ A22 ^^ A23 ^^ A24
  and C3 = A30 ^^ A31 ^^ A32 ^^ A33 ^^ A34
  and C4 = A40 ^^ A41 ^^ A42 ^^ A43 ^^ A44 in
  let D0 = C4 ^^ word_rol C1 1
  and D1 = C0 ^^ word_rol C2 1
  and D2 = C1 ^^ word_rol C3 1
  and D3 = C2 ^^ word_rol C4 1
  and D4 = C3 ^^ word_rol C0 1 in
  let At00 = A00 ^^ D0
  and At01 = A01 ^^ D0
  and At02 = A02 ^^ D0
  and At03 = A03 ^^ D0
  and At04 = A04 ^^ D0
  and At10 = A10 ^^ D1
  and At11 = A11 ^^ D1
  and At12 = A12 ^^ D1
  and At13 = A13 ^^ D1
  and At14 = A14 ^^ D1
  and At20 = A20 ^^ D2
  and At21 = A21 ^^ D2
  and At22 = A22 ^^ D2
  and At23 = A23 ^^ D2
  and At24 = A24 ^^ D2
  and At30 = A30 ^^ D3
  and At31 = A31 ^^ D3
  and At32 = A32 ^^ D3
  and At33 = A33 ^^ D3
  and At34 = A34 ^^ D3
  and At40 = A40 ^^ D4
  and At41 = A41 ^^ D4
  and At42 = A42 ^^ D4
  and At43 = A43 ^^ D4
  and At44 = A44 ^^ D4 in
  let B00 = word_rol At00  0
  and B01 = word_rol At30 28
  and B02 = word_rol At10  1
  and B03 = word_rol At40 27
  and B04 = word_rol At20 62
  and B10 = word_rol At11 44
  and B11 = word_rol At41 20
  and B12 = word_rol At21  6
  and B13 = word_rol At01 36
  and B14 = word_rol At31 55
  and B20 = word_rol At22 43
  and B21 = word_rol At02  3
  and B22 = word_rol At32 25
  and B23 = word_rol At12 10
  and B24 = word_rol At42 39
  and B30 = word_rol At33 21
  and B31 = word_rol At13 45
  and B32 = word_rol At43  8
  and B33 = word_rol At23 15
  and B34 = word_rol At03 41
  and B40 = word_rol At44 14
  and B41 = word_rol At24 61
  and B42 = word_rol At04 18
  and B43 = word_rol At34 56
  and B44 = word_rol At14  2 in
  [(B00 ^^ (~~B10 && B20)) ^^ RCi;
   B10 ^^ (~~B20 && B30);
   B20 ^^ (~~B30 && B40);
   B30 ^^ (~~B40 && B00);
   B40 ^^ (~~B00 && B10);
   B01 ^^ (~~B11 && B21);
   B11 ^^ (~~B21 && B31);
   B21 ^^ (~~B31 && B41);
   B31 ^^ (~~B41 && B01);
   B41 ^^ (~~B01 && B11);
   B02 ^^ (~~B12 && B22);
   B12 ^^ (~~B22 && B32);
   B22 ^^ (~~B32 && B42);
   B32 ^^ (~~B42 && B02);
   B42 ^^ (~~B02 && B12);
   B03 ^^ (~~B13 && B23);
   B13 ^^ (~~B23 && B33);
   B23 ^^ (~~B33 && B43);
   B33 ^^ (~~B43 && B03);
   B43 ^^ (~~B03 && B13);
   B04 ^^ (~~B14 && B24);
   B14 ^^ (~~B24 && B34);
   B24 ^^ (~~B34 && B44);
   B34 ^^ (~~B44 && B04);
   B44 ^^ (~~B04 && B14)]`;;

let keccak = define
 `keccak 0 l = l /\
  keccak (n + 1) l = keccak_round (EL n round_constants) (keccak n l)`;;

remove_interface "~~";; unparse_as_prefix "~~";;
remove_interface "&&";; unparse_as_infix "&&";;
remove_interface "||";; unparse_as_infix "||";;
remove_interface "^^";; unparse_as_infix "^^";;

(* Copied from keccak_spec.ml as well, with its proof.                       *)

let LENGTH_KECCAK = prove
 (`!A i. LENGTH A = 25 ==> LENGTH(keccak i A) = 25`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak; ADD1; keccak_round] THEN
  REPEAT LET_TAC THEN CONV_TAC(LAND_CONV LENGTH_CONV) THEN REFL_TAC);;

let LENGTH_EQ_25 = prove
 (`!l:A list.
        LENGTH l = 25 <=>
        l = [EL 0 l; EL 1 l; EL 2 l; EL 3 l; EL 4 l;
             EL 5 l; EL 6 l; EL 7 l; EL 8 l; EL 9 l;
             EL 10 l; EL 11 l; EL 12 l; EL 13 l; EL 14 l;
             EL 15 l; EL 16 l; EL 17 l; EL 18 l; EL 19 l;
             EL 20 l; EL 21 l; EL 22 l; EL 23 l; EL 24 l]`,
  GEN_TAC THEN EQ_TAC THENL
   [CONV_TAC(LAND_CONV(TOP_DEPTH_CONV num_CONV)) THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONS_11] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC]);;

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
