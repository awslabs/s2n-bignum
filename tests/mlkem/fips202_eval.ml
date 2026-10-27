(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Evaluation of the FIPS 202 functions on concrete inputs by proof, used    *)
(* to check the definitions against standard test vectors.                   *)
(* ========================================================================= *)

needs "common/fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* Round constants as explicit words.                                        *)
(* ------------------------------------------------------------------------- *)

let KECCAK_LFSR_CONV =
  let th0,th1 = CONJ_PAIR keccak_lfsr in
  let cache = Hashtbl.create 300 in
  Hashtbl.add cache 0 th0;
  let rec get n =
    try Hashtbl.find cache n with Not_found ->
    let thp = get (n - 1) in
    let tm = mk_comb(`keccak_lfsr`,mk_small_numeral n) in
    let th = (RAND_CONV num_CONV THENC GEN_REWRITE_CONV I [th1] THENC
              PURE_REWRITE_CONV[thp] THENC WORD_REDUCE_CONV) tm in
    Hashtbl.add cache n th; th in
  fun tm -> match tm with
      Comb(Const("keccak_lfsr",_),n) when is_numeral n ->
        get (Num.int_of_num (dest_numeral n))
    | _ -> failwith "KECCAK_LFSR_CONV";;

let KECCAK_ROUND_CONSTANT_CONV =
  REWRITE_CONV[keccak_round_constant; keccak_rc] THENC
  ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC NUM_REDUCE_CONV THENC
  DEPTH_CONV KECCAK_LFSR_CONV THENC WORD_REDUCE_CONV THENC
  REWRITE_CONV[BITVAL_CLAUSES] THENC NUM_REDUCE_CONV;;

let KECCAK_ROUND_CONSTANTS = map
  (fun i -> KECCAK_ROUND_CONSTANT_CONV
              (mk_comb(`keccak_round_constant`,mk_small_numeral i)))
  (0--23);;

(* ------------------------------------------------------------------------- *)
(* One round, lane by lane, as an explicit expression in the input lanes.    *)
(* ------------------------------------------------------------------------- *)

let KECCAK_RND_LANE_CONV =
  REWRITE_CONV[keccak_rnd; keccak_iota; keccak_chi; keccak_pi; keccak_rho;
               keccak_rho_offset; keccak_theta] THENC
  TOP_DEPTH_CONV let_CONV THENC REWRITE_CONV[] THENC
  NUM_REDUCE_CONV THENC TOP_DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV;;

let KECCAK_RND_LANES =
  map (fun j -> KECCAK_RND_LANE_CONV
      (list_mk_comb(`keccak_rnd i (a:num->num->int64)`,
        [mk_small_numeral (j mod 5); mk_small_numeral (j / 5)]))) (0--24);;

(* ------------------------------------------------------------------------- *)
(* keccak_state(keccak_rnd n (keccak_lanes(word N))) = word N'.              *)
(* ------------------------------------------------------------------------- *)

let KECCAK_ROUND_WORD_CONV tm =
  let n = rand(rator(rand tm)) and lanes = rand(rand tm) in
  let lanethms = map
    (fun j -> (REWRITE_CONV[keccak_lanes] THENC NUM_REDUCE_CONV THENC
               WORD_REDUCE_CONV)
       (list_mk_comb(lanes,[mk_small_numeral (j mod 5);
                            mk_small_numeral (j / 5)]))) (0--24) in
  let rndthms = map (INST [n,`i:num`; lanes,`a:num->num->int64`])
                    KECCAK_RND_LANES in
  let rcth = el (Num.int_of_num(dest_numeral n)) KECCAK_ROUND_CONSTANTS in
  (REWRITE_CONV[keccak_state] THENC
   ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC NUM_REDUCE_CONV THENC
   PURE_REWRITE_CONV rndthms THENC PURE_REWRITE_CONV (rcth::lanethms) THENC
   WORD_REDUCE_CONV THENC NUM_REDUCE_CONV) tm;;

(* ------------------------------------------------------------------------- *)
(* keccak_f1600(word N) = word N'.                                           *)
(* ------------------------------------------------------------------------- *)

let KECCAK_F1600_CONV =
  let pth0 = prove
   (`keccak_state (keccak_rounds 0 (keccak_lanes s)) = s`,
    REWRITE_TAC[keccak_rounds; KECCAK_STATE_LANES]) in
  fun tm ->
    match tm with
      Comb(Const("keccak_f1600",_),s) ->
        let step k th =
          let th1 = SPECL [s; mk_small_numeral k] KECCAK_F1600_ROUND_WORDS in
          let th2 = CONV_RULE(RAND_CONV(PURE_REWRITE_CONV[th] THENC
                                        KECCAK_ROUND_WORD_CONV)) th1 in
          CONV_RULE(LAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV
                      NUM_SUC_CONV)))) th2 in
        let rec iter k th = if k = 24 then th else iter (k + 1) (step k th) in
        let th = iter 0 (INST [s,`s:1600 word`] pth0) in
        TRANS (REWR_CONV keccak_f1600 tm) th
    | _ -> failwith "KECCAK_F1600_CONV";;

(* ------------------------------------------------------------------------- *)
(* Faster: iterate the rounds on explicit tables of 25 lane values, using    *)
(* the fact that everything only depends on the lanes with x,y < 5.          *)
(* ------------------------------------------------------------------------- *)

let keccak_agree = new_definition
 `keccak_agree (a:num->num->int64) b <=>
        !x y. x < 5 /\ y < 5 ==> a x y = b x y`;;

let KECCAK_AGREE_EXPAND = prove
 (`keccak_agree a b <=>
   a 0 0 = b 0 0 /\ a 1 0 = b 1 0 /\ a 2 0 = b 2 0 /\ a 3 0 = b 3 0 /\
   a 4 0 = b 4 0 /\
   a 0 1 = b 0 1 /\ a 1 1 = b 1 1 /\ a 2 1 = b 2 1 /\ a 3 1 = b 3 1 /\
   a 4 1 = b 4 1 /\
   a 0 2 = b 0 2 /\ a 1 2 = b 1 2 /\ a 2 2 = b 2 2 /\ a 3 2 = b 3 2 /\
   a 4 2 = b 4 2 /\
   a 0 3 = b 0 3 /\ a 1 3 = b 1 3 /\ a 2 3 = b 2 3 /\ a 3 3 = b 3 3 /\
   a 4 3 = b 4 3 /\
   a 0 4 = b 0 4 /\ a 1 4 = b 1 4 /\ a 2 4 = b 2 4 /\ a 3 4 = b 3 4 /\
   a 4 4 = b 4 4`,
  REWRITE_TAC[keccak_agree; GSYM IMP_IMP; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJ_ACI]);;

let KECCAK_AGREE_TRANS = prove
 (`!a b c. keccak_agree a b /\ keccak_agree b c ==> keccak_agree a c`,
  REWRITE_TAC[keccak_agree] THEN MESON_TAC[]);;

let KECCAK_AGREE_RND = prove
 (`!n a b. keccak_agree a b
           ==> keccak_agree (keccak_rnd n a) (keccak_rnd n b)`,
  REWRITE_TAC[keccak_agree; KECCAK_RND_LOCAL]);;

let KECCAK_AGREE_ROUNDS = prove
 (`!n a b. keccak_agree a b
           ==> keccak_agree (keccak_rounds n a) (keccak_rounds n b)`,
  INDUCT_TAC THEN REWRITE_TAC[keccak_rounds] THEN
  ASM_MESON_TAC[KECCAK_AGREE_RND]);;

let KECCAK_F1600_AGREE = prove
 (`!s a. keccak_agree (keccak_lanes s) a
         ==> keccak_f1600 s = keccak_state(keccak_rounds 24 a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_f1600] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN
  MP_TAC(SPECL [`24`; `keccak_lanes s`; `a:num->num->int64`]
               KECCAK_AGREE_ROUNDS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[keccak_agree]);;

let KECCAK_STATE_AGREE = prove
 (`!a b. keccak_agree a b ==> keccak_state a = keccak_state b`,
  REWRITE_TAC[keccak_agree; KECCAK_STATE_EQ]);;

let KECCAK_ROUNDS_STEP = prove
 (`!n a b c. keccak_agree (keccak_rounds n a) b /\
             keccak_agree (keccak_rnd n b) c
             ==> keccak_agree (keccak_rounds (SUC n) a) c`,
  REWRITE_TAC[keccak_rounds] THEN
  MESON_TAC[KECCAK_AGREE_RND; KECCAK_AGREE_TRANS]);;

(* Explicit tables of 25 lanes, and fast evaluation of one round on them.    *)

let keccak_table = new_definition
 `keccak_table (l:int64 list) x y = EL (x + 5 * y) l`;;

let keccak_table_vars =
  map (fun j -> mk_var("v"^string_of_int j,`:int64`)) (0--24);;

let keccak_table_tm =
  mk_comb(`keccak_table`,mk_list(keccak_table_vars,`:int64`));;

let KECCAK_TABLE_LANES =
  map (fun j -> (REWRITE_CONV[keccak_table] THENC NUM_REDUCE_CONV THENC
                  EL_CONV)
          (list_mk_comb(keccak_table_tm,[mk_small_numeral(j mod 5);
                                         mk_small_numeral(j / 5)]))) (0--24);;

let KECCAK_RND_TABLE =
  let rcvar = `rc:int64` in
  map (fun th ->
    let th1 = INST [keccak_table_tm,`a:num->num->int64`] th in
    let th2 = CONV_RULE(RAND_CONV(PURE_REWRITE_CONV KECCAK_TABLE_LANES)) th1 in
    let asm = mk_eq(`keccak_round_constant i`,rcvar) in
    DISCH asm (PURE_REWRITE_RULE[ASSUME asm] th2)) KECCAK_RND_LANES;;

(* keccak_agree (keccak_rnd k (keccak_table l)) (keccak_table l') for an     *)
(* explicit list l of constants, returning the theorem and l'.               *)

let KECCAK_RND_TABLE_RULE k l =
  let cs = dest_list l in
  let rcth = el k KECCAK_ROUND_CONSTANTS in
  let inst = (rand(concl rcth),`rc:int64`)::(mk_small_numeral k,`i:num`)::
             zip cs keccak_table_vars in
  let lhs = map (fun th -> CONV_RULE(RAND_CONV WORD_REDUCE_CONV)
                             (MP (INST inst th) rcth)) KECCAK_RND_TABLE in
  let l' = mk_list(map (rand o concl) lhs,`:int64`) in
  let rhs = map (INST (zip (dest_list l') keccak_table_vars))
                KECCAK_TABLE_LANES in
  let conjs = map2 (fun th1 th2 -> TRANS th1 (SYM th2)) lhs rhs in
  let a = lhand(concl(hd conjs)) in
  let ath = INST [rator(rator a),`a:num->num->int64`;
                  mk_comb(`keccak_table`,l'),`b:num->num->int64`]
                 KECCAK_AGREE_EXPAND in
  EQ_MP (SYM ath) (end_itlist CONJ conjs),l';;

let KECCAK_F1600_CONV' tm =
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
      let thf = MATCH_MP KECCAK_F1600_AGREE th0 in
      let a0 = mk_comb(`keccak_table`,l0) in
      let base = INST [a0,`a:num->num->int64`]
       (prove(`keccak_agree (keccak_rounds 0 a) a`,
              REWRITE_TAC[keccak_rounds; keccak_agree])) in
      let rec iter k th l =
        if k = 24 then th,l else
        let th1,l' = KECCAK_RND_TABLE_RULE k l in
        let th2 = MATCH_MP KECCAK_ROUNDS_STEP (CONJ th th1) in
        let th3 =
          CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV NUM_SUC_CONV))) th2 in
        iter (k + 1) th3 l' in
      let thr,lf = iter 0 base l0 in
      let th5 = TRANS thf (MATCH_MP KECCAK_STATE_AGREE thr) in
      let fths = map (INST (zip (dest_list lf) keccak_table_vars))
                     KECCAK_TABLE_LANES in
      CONV_RULE(RAND_CONV(REWRITE_CONV[keccak_state] THENC
                          ONCE_DEPTH_CONV EXPAND_NSUM_CONV THENC
                          NUM_REDUCE_CONV THENC PURE_REWRITE_CONV fths THENC
                          WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) th5
  | _ -> failwith "KECCAK_F1600_CONV'";;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the sponge and of the SHA-3 functions.                      *)
(* ------------------------------------------------------------------------- *)

let REPLICATE_CONV =
  let [pth0;pth1] = CONJUNCTS REPLICATE in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("REPLICATE",_),n),x) ->
        if is_numeral n && dest_numeral n =/ num 0 then REWR_CONV pth0 tm
        else
          let th1 = (LAND_CONV num_CONV THENC REWR_CONV pth1) tm in
          CONV_RULE(RAND_CONV(RAND_CONV conv)) th1
    | _ -> failwith "REPLICATE_CONV" in
  conv;;

let NUM_OF_BYTELIST_CONV =
  let [pth0;pth1] = CONJUNCTS num_of_bytelist in
  let rec conv tm =
    match tm with
      Comb(Const("num_of_bytelist",_),l) ->
        if l = `[]:byte list` then pth0 else
        let th1 = REWR_CONV (SPEC_ALL pth1) tm in
        let th2 = CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV conv))) th1 in
        CONV_RULE(RAND_CONV(WORD_REDUCE_CONV THENC NUM_REDUCE_CONV)) th2
    | _ -> failwith "NUM_OF_BYTELIST_CONV" in
  conv;;

(* The permutation evaluator used by the sponge evaluation; keccak_bridge.ml *)
(* replaces it by a faster one.                                              *)

let keccak_f1600_conv = ref KECCAK_F1600_CONV';;

let KECCAK_ABSORB_CONV =
  let [pth0;pth1] = CONJUNCTS keccak_absorb in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("keccak_absorb",_),r),p),j) ->
        if dest_numeral j =/ num 0 then
          PART_MATCH lhs pth0 tm
        else
          let th1 = (RAND_CONV num_CONV THENC REWR_CONV pth1) tm in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV conv))) th1 in
          let th3 = CONV_RULE(RAND_CONV(RAND_CONV
                      (NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))) th2 in
          CONV_RULE(RAND_CONV (!keccak_f1600_conv)) th3
    | _ -> failwith "KECCAK_ABSORB_CONV" in
  conv;;

let KECCAK_SQUEEZE_CONV =
  let [pth0;pth1] = CONJUNCTS keccak_squeeze in
  let cache = ref [] in
  let rec conv tm =
    try assoc tm (!cache) with Failure _ ->
    let th =
      match tm with
        Comb(Comb(Const("keccak_squeeze",_),t),s) ->
          if dest_numeral t =/ num 0 then PART_MATCH lhs pth0 tm
          else
            let th1 = (LAND_CONV num_CONV THENC REWR_CONV pth1) tm in
            let th2 = CONV_RULE(RAND_CONV(RAND_CONV conv)) th1 in
            CONV_RULE(RAND_CONV (!keccak_f1600_conv)) th2
      | _ -> failwith "KECCAK_SQUEEZE_CONV" in
    cache := (tm,th)::(!cache); th in
  conv;;

let LET_EVAL_CONV conv = RAND_CONV conv THENC let_CONV;;

(* keccak_sponge c d m = \i. ... with the absorbed state as a word.          *)

let KECCAK_CONV tm =
  let padconv =
    REWRITE_CONV[keccak_pad] THENC NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV REPLICATE_CONV THENC REWRITE_CONV[APPEND] in
  (REWR_CONV keccak_sponge THENC
   LET_EVAL_CONV NUM_REDUCE_CONV THENC
   LET_EVAL_CONV (ONCE_DEPTH_CONV LENGTH_CONV THENC padconv) THENC
   LET_EVAL_CONV (ONCE_DEPTH_CONV NUM_OF_BYTELIST_CONV THENC
                  ONCE_DEPTH_CONV LENGTH_CONV THENC NUM_REDUCE_CONV THENC
                  KECCAK_ABSORB_CONV)) tm;;

(* Evaluate list_of_seq (keccak_sponge c d m) n, or more generally           *)
(* list_of_seq (\i. keccak_sponge c d m (i + a)) n, to an explicit list.     *)

let KECCAK_OUTPUT_CONV tm =
  let th1 = ONCE_DEPTH_CONV KECCAK_CONV tm in
  CONV_RULE(RAND_CONV(LIST_OF_SEQ_CONV THENC REWRITE_CONV[] THENC
                      NUM_REDUCE_CONV THENC
                      ONCE_DEPTH_CONV KECCAK_SQUEEZE_CONV THENC
                      WORD_REDUCE_CONV)) th1;;

let SHA3_256_CONV = REWR_CONV sha3_256 THENC KECCAK_OUTPUT_CONV;;
let SHA3_512_CONV = REWR_CONV sha3_512 THENC KECCAK_OUTPUT_CONV;;
