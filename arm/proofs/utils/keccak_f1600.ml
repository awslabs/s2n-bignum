(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The Keccak-f[1600] permutation of common/fips202.ml, on the state as a    *)
(* 1600-bit word, is the same as the 24 rounds "keccak 24" on the list of    *)
(* its 25 lanes in keccak_spec.ml, which specify the code for Keccak. This   *)
(* is KECCAK_F1600_BRIDGE, proved as in tests/mlkem/keccak_bridge.ml (with   *)
(* parts of tests/mlkem/fips202_eval.ml), but using keccak_spec.ml itself    *)
(* rather than a copy of its definitions. For a state in memory, the         *)
(* 1600-bit word is the one read by wbytes. The lemmas about the padding and *)
(* the sponge are in keccak_fips202.ml, which loads this file.               *)
(* ========================================================================= *)

needs "common/fips202.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

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

let KECCAK_ROUND_CONSTANTS_TABLE = prove
 (`!i. i < 24 ==> EL i round_constants = keccak_round_constant i`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC KECCAK_ROUND_CONSTANTS THEN
  REWRITE_TAC[round_constants] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Agreement of two lane functions on the lanes with x,y < 5, which is all   *)
(* that the rounds depend on, and tables of lanes from lists of 25 lanes.    *)
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

let keccak_table = new_definition
 `keccak_table (l:int64 list) x y = EL (x + 5 * y) l`;;

(* ------------------------------------------------------------------------- *)
(* One round of keccak_rnd on a table of 25 lane variables, lane by lane, is *)
(* the same as keccak_round on the list of them.                             *)
(* ------------------------------------------------------------------------- *)

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
  let lane_conv =
    REWRITE_CONV[keccak_rnd; keccak_iota; keccak_chi; keccak_pi; keccak_rho;
                 keccak_rho_offset; keccak_theta] THENC
    TOP_DEPTH_CONV let_CONV THENC REWRITE_CONV[] THENC
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV EL_CONV THENC NUM_REDUCE_CONV in
  let lanes =
    map (fun j -> lane_conv
        (list_mk_comb(`keccak_rnd i (a:num->num->int64)`,
          [mk_small_numeral (j mod 5); mk_small_numeral (j / 5)]))) (0--24) in
  let rcvar = `rc:int64` in
  map (fun th ->
    let th1 = INST [keccak_table_tm,`a:num->num->int64`] th in
    let th2 = CONV_RULE(RAND_CONV(PURE_REWRITE_CONV KECCAK_TABLE_LANES)) th1 in
    let asm = mk_eq(`keccak_round_constant i`,rcvar) in
    DISCH asm (PURE_REWRITE_RULE[ASSUME asm] th2)) lanes;;

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

(* ------------------------------------------------------------------------- *)
(* Hence the bridge between the rounds and the whole permutation.            *)
(* ------------------------------------------------------------------------- *)

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
(* A list of 25 lanes and a state in memory as a 1600-bit word.              *)
(* ------------------------------------------------------------------------- *)

let KECCAK_STATE_TABLE = prove
 (`!l:int64 list.
        LENGTH l = 25
        ==> keccak_state(keccak_table l) = word(num_of_wordlist l)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM KECCAK_STATE_LANES] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[keccak_table; keccak_lanes] THEN
  ASM_SIMP_TAC[EL_NUM_OF_WORDLIST; ARITH_RULE
   `x < 5 /\ y < 5 ==> x + 5 * y < 25`] THEN
  REWRITE_TAC[word_subword; GSYM VAL_EQ; VAL_WORD; DIMINDEX_64;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  MP_TAC(ISPEC `l:int64 list` NUM_OF_WORDLIST_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

let READ_MEMORY_WBYTES_KECCAK = prove
 (`!a (S:1600 word) s:armstate.
        read (memory :> wbytes a) s = S <=>
        wordlist_from_memory(a,25) s =
        (wordlist_of_num 25 (val S):int64 list)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `num_of_wordlist:int64 list->num`) THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
  MP_TAC(ISPECL [`a:int64`; `200`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

let WORDLIST_FROM_MEMORY_KECCAK = prove
 (`!a l s:armstate.
        wordlist_from_memory(a,25) s = l
        ==> read (memory :> wbytes a) s = keccak_state(keccak_table l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[KECCAK_STATE_TABLE; LENGTH_WORDLIST_FROM_MEMORY] THEN
  GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; NUM_OF_WORDLIST_FROM_MEMORY;
              DIMINDEX_8; DIMINDEX_64; DIMINDEX_CONV `dimindex(:1600)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `200`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The permutation of a state in memory, in the form of the code proofs.     *)
(* ------------------------------------------------------------------------- *)

let KECCAK_F1600_MEMORY = prove
 (`!a (S:1600 word) s:armstate.
        wordlist_from_memory(a,25) s = keccak 24 (wordlist_of_num 25 (val S))
        ==> read (memory :> wbytes a) s = keccak_f1600 S`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WORDLIST_FROM_MEMORY_KECCAK) THEN
  W(MP_TAC o PART_MATCH (rand o rand) KECCAK_F1600_BRIDGE o lhand o snd) THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_STATE_TABLE; LENGTH_WORDLIST_OF_NUM] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; WORD_VAL]);;
