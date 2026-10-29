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
(* 1600-bit word is the one read by wbytes. There are also lemmas about the  *)
(* padding and the blocks of the padded message, as numbers, for             *)
(* keccak_absorb, and about the output of keccak_sponge.                     *)
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

(* ------------------------------------------------------------------------- *)
(* The padding as a number. For a message of mlen bytes as a number M, the   *)
(* padded message in keccak_sponge is the number                             *)
(* M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r d mlen), whose blocks *)
(* are the whole blocks of M, then the rest of M with the padding.           *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let NUM_OF_BYTELIST_REPLICATE_0 = prove
 (`!n. num_of_bytelist (REPLICATE n (word 0:byte)) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; num_of_bytelist; VAL_WORD_0] THEN ARITH_TAC);;

let KECCAK_PAD_NUM = prove
 (`!r d len.
        0 < r /\ d < 128
        ==> num_of_bytelist(keccak_pad r d len) =
            if len MOD r = r - 1 then d + 128
            else d + 2 EXP (8 * (r - len MOD r - 1)) * 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; NUM_OF_BYTELIST_APPEND;
                  NUM_OF_BYTELIST_REPLICATE_0; LENGTH_REPLICATE;
                  VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `d < 128 ==> d < 256 /\ d + 128 < 256`] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r - len MOD r - 1 = (r - len MOD r - 2) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let KECCAK_PAD_BOUND = prove
 (`!r d len.
        0 < r /\ d < 128
        ==> num_of_bytelist(keccak_pad r d len) < 2 EXP (8 * (r - len MOD r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. r - len MOD r = k + 1` (X_CHOOSE_THEN `k:num`
   (fun th -> REWRITE_TAC[th; ADD_SUB] THEN ASSUME_TAC th))
  THENL [EXISTS_TAC `r - len MOD r - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~(2 EXP (8 * k) = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `k = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `d < 128` THEN ARITH_TAC;
    SPEC_TAC(`2 EXP (8 * k)`,`e:num`) THEN
    UNDISCH_TAC `d < 128` THEN ARITH_TAC]);;

let WORD_XOR_DISJOINT_ADD = prove
 (`!a b k. a < 2 EXP k
           ==> word_xor (word a:N word) (word(2 EXP k * b)) =
               word(a + 2 EXP k * b)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[WORD_ADD] THEN MATCH_MP_TAC WORD_ADD_XOR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < k:num` THENL
   [SUBGOAL_THEN `(2 EXP k * b) DIV 2 EXP i = 2 * 2 EXP (k - i - 1) * b`
     (fun th -> REWRITE_TAC[th; ODD_MULT; ARITH_ODD]) THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; EXP_EQ_0; ARITH_EQ;
                ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    SUBGOAL_THEN `k = (k - i - 1) + 1 + i`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]];
    SUBGOAL_THEN `a DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ARITH_ODD])
    THEN MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP k` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

let KECCAK_BLOCK_FULL = prove
 (`!M pad mlen r k.
        r * (k + 1) <= mlen
        ==> ((M + 2 EXP (8 * mlen) * pad) DIV 2 EXP (8 * r * k)) MOD
            2 EXP (8 * r) =
            (M DIV 2 EXP (8 * r * k)) MOD 2 EXP (8 * r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?e. mlen = r * k + r + e` (X_CHOOSE_THEN `e:num` SUBST1_TAC)
  THENL [EXISTS_TAC `mlen - r * (k + 1)` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `M + (a * b * c) * p = (b * c * p) * a + M`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `b * c * p + x = (c * p) * b + x`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let KECCAK_BLOCK_LAST = prove
 (`!M pad mlen r.
        0 < r /\ M < 2 EXP (8 * mlen) /\
        pad < 2 EXP (8 * (r - mlen MOD r))
        ==> ((M + 2 EXP (8 * mlen) * pad) DIV
             2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * r) =
            M DIV 2 EXP (8 * r * mlen DIV r) + 2 EXP (8 * mlen MOD r) * pad`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  MAP_EVERY ABBREV_TAC [`q = mlen DIV r`; `t = mlen MOD r`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * q * r = 8 * r * q`] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `M + (a * b) * p = (b * p) * a + M`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * q * r) < 2 EXP (8 * t)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    UNDISCH_TAC `M < 2 EXP (8 * (q * r + t))` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (8 * r) = 2 EXP (8 * t) * 2 EXP (8 * (r - t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (8 * t) + 2 EXP (8 * t) * pad` THEN
  ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
  REWRITE_TAC[ARITH_RULE `a + a * b = a * (b + 1)`; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The output of keccak_sponge in terms of the state after absorbing all but *)
(* the last permutation, as for mlk_keccak_absorb_once in mlkem-native, and  *)
(* the first n bytes of it, or of any block of it, for n up to the rate.     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_KECCAK_PAD = prove
 (`!r d len. 0 < r ==> LENGTH(keccak_pad r d len) = r - len MOD r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  ASM_ARITH_TAC);;

let KECCAK_SPONGE_ABSORB = prove
 (`!r d (m:byte list).
        0 < r
        ==> keccak_absorb r
             (num_of_bytelist(APPEND m (keccak_pad r d (LENGTH m))))
             (LENGTH(APPEND m (keccak_pad r d (LENGTH m))) DIV r) =
            keccak_f1600
             (word_xor
               (keccak_absorb r
                 (num_of_bytelist m +
                  2 EXP (8 * LENGTH m) *
                  num_of_bytelist(keccak_pad r d (LENGTH m)))
                 (LENGTH m DIV r))
               (word((num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad r d (LENGTH m))) DIV
                     2 EXP (8 * r * LENGTH m DIV r) MOD 2 EXP (8 * r))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_APPEND; LENGTH_KECCAK_PAD] THEN
  SUBGOAL_THEN
   `(LENGTH(m:byte list) + r - LENGTH m MOD r) DIV r = SUC(LENGTH m DIV r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    REWRITE_TAC[keccak_absorb]]);;

let KECCAK_SQUEEZE_F1600 = prove
 (`!k S. keccak_f1600(keccak_squeeze k S) = keccak_squeeze k (keccak_f1600 S)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze]);;

let KECCAK_SPONGE_SQUEEZE = prove
 (`!c d (m:byte list) r P i.
        (1600 - c) DIV 8 = r /\ 0 < r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> keccak_sponge c d m i =
            word_subword
             (keccak_squeeze (i DIV r + 1)
               (word_xor (keccak_absorb r P (LENGTH m DIV r))
                         (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                               2 EXP (8 * r)))))
             (8 * (i MOD r),8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_sponge] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[KECCAK_SPONGE_ABSORB] THEN
  REWRITE_TAC[GSYM ADD1; keccak_squeeze; KECCAK_SQUEEZE_F1600]);;

let NUM_OF_BYTELIST_STATE_BYTES = prove
 (`!(S:1600 word) n.
        n <= 200
        ==> num_of_bytelist(list_of_seq (\i. word_subword S (8 * i,8)) n) =
            val S MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `SUC n <= 200 ==> n <= 200`] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD_SUBWORD; DIMINDEX_8;
              ARITH_RULE `MIN 8 8 = 8`] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let KECCAK_SPONGE_BYTES = prove
 (`!c d (m:byte list) r P n.
        (1600 - c) DIV 8 = r /\ 0 < r /\ n <= r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> num_of_bytelist(list_of_seq (keccak_sponge c d m) n) =
            val(keccak_f1600
                 (word_xor (keccak_absorb r P (LENGTH m DIV r))
                           (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                                 2 EXP (8 * r))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(1600 - c) DIV 8 = r`; `n <= r`] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let sv = rand(lhand(rand w)) in
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(`num_of_bytelist`,
      list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
       [mk_abs(`i:num`,
          list_mk_comb(`word_subword:1600 word->num#num->byte`,
            [sv; `8 * i,8`]));
        `n:num`])))) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:num`; `d:num`; `m:byte list`; `r:num`; `P:num`; `i:num`]
                 KECCAK_SPONGE_SQUEEZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `i DIV r = 0 /\ i MOD r = i` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[ADD_CLAUSES; num_CONV `1`; keccak_squeeze]];
    MATCH_MP_TAC NUM_OF_BYTELIST_STATE_BYTES THEN ASM_REWRITE_TAC[]]);;

let NUM_OF_BYTELIST_LIST_OF_SEQ_ADD = prove
 (`!(f:num->byte) a b.
        num_of_bytelist(list_of_seq f (a + b)) =
        num_of_bytelist(list_of_seq f a) +
        2 EXP (8 * a) * num_of_bytelist(list_of_seq (\j. f(a + j)) b)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; num_of_bytelist; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
                  num_of_bytelist] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES; ADD_CLAUSES] THEN
  ARITH_TAC);;

let KECCAK_SPONGE_BLOCK = prove
 (`!c d (m:byte list) r P k n.
        (1600 - c) DIV 8 = r /\ 0 < r /\ n <= r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> num_of_bytelist
             (list_of_seq (\j. keccak_sponge c d m (r * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor (keccak_absorb r P (LENGTH m DIV r))
                           (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                                 2 EXP (8 * r))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(1600 - c) DIV 8 = r`; `n <= r`] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let sv = rand(lhand(rand w)) in
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(`num_of_bytelist`,
      list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
       [mk_abs(`j:num`,
          list_mk_comb(`word_subword:1600 word->num#num->byte`,
            [sv; `8 * j,8`]));
        `n:num`])))) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:num`; `d:num`; `m:byte list`; `r:num`; `P:num`;
                  `r * k + j`] KECCAK_SPONGE_SQUEEZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(r * k + j) DIV r = k /\ (r * k + j) MOD r = j`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC];
      REFL_TAC];
    MATCH_MP_TAC NUM_OF_BYTELIST_STATE_BYTES THEN ASM_REWRITE_TAC[]]);;
