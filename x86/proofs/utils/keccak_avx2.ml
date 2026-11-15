(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the AVX2 Keccak-f1600 permutations of one state,  *)
(* sha3_keccak_f1600_alt and sha3_keccak_f1600_alt2: each keeps the state in *)
(* ymm0-ymm6, counts the rounds down in a 32-bit register and reads rotation *)
(* counts from a 384-byte table at tab.                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/keccak_spec.ml";;

let KECCAK_AVX2_JOIN_EQ = prove
 (`!a b c d e f g h.
     word_join (word_join (a:int64) (b:int64):int128)
               (word_join (c:int64) (d:int64):int128):int256 =
     word_join (word_join (e:int64) (f:int64):int128)
               (word_join (g:int64) (h:int64):int128) <=>
     a = e /\ b = f /\ c = g /\ d = h`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `\x:int256. [word_subword x (192,64):int64; word_subword x (128,64);
                word_subword x (64,64); word_subword x (0,64)]`) THEN
  BETA_TAC THEN REWRITE_TAC[WORD_SUBWORD_JOIN_EXTRACT_64; CONS_11]);;

(*** The round counter in eax ***)

let KECCAK_AVX2_COUNTER = prove
 (`!i. i < 24
       ==> word_zx (word_sub (word_zx (word (24 - i):int64):int32) (word 1))
           :int64 = word (24 - (i + 1)) /\
           (val (word_sub (word_zx (word (24 - i):int64):int32) (word 1)) = 0
            <=> i + 1 = 24)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let READ_MEMORY_BYTES256_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes256(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES256_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[GSYM(NUM_REDUCE_CONV `2 EXP (8 * 32)`);
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** The twelve rows of the tables, as read in each round ***)

let KECCAK_AVX2_TABLE_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes (word tab,384)) s0 = n`)
           (concl th)
    then MP_TAC(end_itlist CONJ (map (fun k ->
           MATCH_MP READ_MEMORY_BYTES256_OF_NUM
            (CONJ th (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral(32 * k)) `32`)
               `384`))))
           (0--11)))
    else NO_TAC) THEN
  CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC;;

(* ------------------------------------------------------------------------- *)
(* The simulation of a round splits the value of each register written into  *)
(* its four 64-bit lanes, each a simple function of the lanes of the inputs  *)
(* of the instruction, and abbreviates each lane that is not a variable or a *)
(* constant as a new variable y<n>, so that the terms do not grow. At the    *)
(* end of the round the abbreviations are expanded, and each lane of the     *)
(* result is compared with that of keccak_round by KECCAK_BITBLAST_TAC.      *)
(* ------------------------------------------------------------------------- *)

let KECCAK_AVX2_JOIN32 = prove
 (`!x:N word p.
        word_join (word_subword x (p + 32,32):int32)
                  (word_subword x (p,32):int32):int64 =
        word_subword x (p,64)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_JOIN; BIT_WORD_SUBWORD;
              DIMINDEX_32; DIMINDEX_64; ARITH_RULE `!n. MIN n n = n`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p + 32) + i - 32 = p + i /\ i - 32 < 32`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(*** Two adjacent 32-bit subwords (from VPBLENDD) as one of 64 bits ***)

let KECCAK_AVX2_JOIN32_CONV tm =
  match tm with
    Comb(Comb(Const("word_join",_),Comb(Comb(Const("word_subword",_),x),pa)),
         Comb(Comb(Const("word_subword",_),x'),pb)) when x = x' ->
      let a,_ = dest_pair pa and p,_ = dest_pair pb in
      if dest_small_numeral a <> dest_small_numeral p + 32 then
        failwith "KECCAK_AVX2_JOIN32_CONV" else
      let th = CONV_RULE(LAND_CONV(DEPTH_CONV NUM_ADD_CONV))
                (ISPECL [x; p] KECCAK_AVX2_JOIN32) in
      if lhs(concl th) = tm then th else failwith "KECCAK_AVX2_JOIN32_CONV"
  | _ -> failwith "KECCAK_AVX2_JOIN32_CONV";;

let KECCAK_AVX2_SUBWORD_COND_CONV th =
  let conv = DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV in
  fun tm ->
    let th1 = PART_MATCH (lhs o rand) th tm in
    CONV_RULE(RAND_CONV conv)
      (MP th1 (EQT_ELIM(conv(lhand(concl th1)))));;

let KECCAK_AVX2_LANE_CONV =
  TOP_DEPTH_CONV
   (KECCAK_AVX2_JOIN32_CONV ORELSEC
    REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    REWR_CONV WORD_SUBWORD_XOR ORELSEC
    KECCAK_AVX2_SUBWORD_COND_CONV WORD_SUBWORD_NOT ORELSEC
    KECCAK_AVX2_SUBWORD_COND_CONV WORD_SUBWORD_DUPLICATE ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let KECCAK_AVX2_SPLIT = prove
 (`!y:int256.
        y = word_join
             (word_join (word_subword y (192,64):int64)
                        (word_subword y (128,64):int64):int128)
             (word_join (word_subword y (64,64):int64)
                        (word_subword y (0,64):int64):int128)`,
  BITBLAST_TAC);;

let keccak_avx2_atom t =
  is_var t ||
  (is_comb t && is_const(rator t) && name_of(rator t) = "word" &&
   is_numeral(rand t));;

let keccak_avx2_lanes_of t =
  let h,l = dest_binop `word_join:int128->int128->int256` t in
  let h1,h0 = dest_binop `word_join:int64->int64->int128` h
  and l1,l0 = dest_binop `word_join:int64->int64->int128` l in
  [h1;h0;l1;l0];;

let keccak_avx2_lane_form t =
  try forall keccak_avx2_atom (keccak_avx2_lanes_of t)
  with Failure _ -> false;;

let keccak_avx2_lanes = ref 0;;

let KECCAK_AVX2_LANE_ABBREV_TAC k (asl,w) =
  let sv = mk_var("s"^string_of_int k,`:x86state`) in
  let is_target th =
    let c = concl th in
    is_eq c && type_of(lhs c) = `:int256` &&
    (match lhs c with
       Comb(Comb(Const("read",_),Const(n,_)),s) ->
         s = sv && String.length n > 3 && String.sub n 0 3 = "YMM"
     | _ -> false) &&
    not(keccak_avx2_lane_form(rhs c)) in
  match filter is_target (map snd asl) with
    [] -> ALL_TAC (asl,w)
  | th::_ ->
      let sth = CONV_RULE(RAND_CONV(BINOP_CONV(BINOP_CONV
                  KECCAK_AVX2_LANE_CONV)))
                 (SPEC (rhs(concl th)) KECCAK_AVX2_SPLIT) in
      let abv = setify(filter (not o keccak_avx2_atom)
                  (keccak_avx2_lanes_of(rhs(concl sth)))) in
      let mk1 e = (incr keccak_avx2_lanes;
                   mk_eq(mk_var("y"^string_of_int(!keccak_avx2_lanes),
                                `:int64`),e)) in
      (UNDISCH_THEN (concl th) (K ALL_TAC) THEN
       MP_TAC(TRANS th sth) THEN
       MAP_EVERY (fun e -> ABBREV_TAC(mk1 e)) abv THEN
       DISCH_TAC) (asl,w);;

(*** The simplification of the SIMD operations in the new value of a
 *** register, as SIMD_SIMPLIFY_TAC[] of common/mlkem_mldsa.ml
 ***)

let KECCAK_AVX2_SIMPLIFY_TAC =
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV
     (TOP_DEPTH_CONV
       (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
      DEPTH_CONV WORD_NUM_RED_CONV)) o
    check (can (term_match [] `read X (s:x86state):int256 = whatever`) o
           concl)));;

(*** The abbreviations of the lanes, to expand at the end. ABBREV_TAC also
 *** rewrites the older assumptions, so where a lane is computed twice the
 *** definition of the first abbreviation becomes y<new> = y<old>: the goal
 *** is rewritten with all the definitions until none applies, so their
 *** order does not matter.
 ***)

let keccak_avx2_lane_def c =
  is_eq c && is_var(rhs c) && String.sub (name_of(rhs c)) 0 1 = "y" &&
  not(can (find_term (fun t -> is_const t && name_of t = "read")) (lhs c));;

let KECCAK_AVX2_EXPAND_TAC (asl,w as gl) =
  PURE_REWRITE_TAC
   (map (SYM o snd) (filter (keccak_avx2_lane_def o concl o snd) asl)) gl;;

(*** The branch of the loop and the addresses of the tables ***)

let KECCAK_AVX2_BRANCH = prove
 (`!i. i < 24
       ==> (~(val (word_zx (word (24 - i):int64):int32) = val (word 1:int32))
            <=> i + 1 < 24)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let KECCAK_AVX2_FOLD_TAC =
  IMP_REWRITE_TAC[RIP_REL_ADDR_FOLD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD];;
