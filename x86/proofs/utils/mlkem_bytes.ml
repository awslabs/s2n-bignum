(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Byte arrays given as numbers, as in mlkem_encode and mlkem_decode of      *)
(* common/fips203/fips203.ml, for the proofs of the ML-KEM functions. Most   *)
(* of these are from the proofs of mlkem-native's compiled code on the mlkem *)
(* branch of jargh/s2n-bignum-dev.                                           *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let DIV_MOD_EXP_LOW = prove
 (`!x m k l. k + l <= m
             ==> ((x MOD 2 EXP m) DIV 2 EXP k) MOD 2 EXP l =
                 (x DIV 2 EXP k) MOD 2 EXP l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k + l <= m ==> MIN m (k + l) = k + l`]);;

let WORD_SUBWORD_WORD = prove
 (`!x k l. k + l <= dimindex(:N)
           ==> word_subword (word x:N word) (k,l):M word =
               word((x DIV 2 EXP k) MOD 2 EXP l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[DIV_MOD_EXP_LOW]);;

let BYTE_BIT = prove
 (`!n m k. k < 8
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 256) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `256 = 2 EXP 8`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 8 ==> MIN 8 (k + 1) = k + 1`]);;

let NSUM_LT_ADD = prove
 (`!f m n. nsum {i | i < m + n} f =
           nsum {i | i < m} f + nsum {i | i < n} (\i. f(m + i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NSUM_CLAUSES_NUMSEG_LT; ADD_ASSOC]);;

let BYTES_BITBLAST_TAC (asl,w) =
  let bts = setify (find_terms (fun t ->
     type_of t = `:byte` &&
     can (term_match [] `word(x MOD 256):byte`) t) w) in
  let vs = map (fun _ -> genvar `:byte`) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;

let QWORD_BIT_ALT = prove
 (`!n i. (n DIV 2 EXP i) MOD 2 =
         (((n DIV 2 EXP (64 * (i DIV 64))) MOD 2 EXP 64) DIV 2 EXP (i MOD 64))
         MOD 2`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
   [MATCH_MP (ARITH_RULE `~(64 = 0) ==> i = 64 * i DIV 64 + i MOD 64`)
     (ARITH_RULE `~(64 = 0)`)] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP (64 * i DIV 64)`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN 64 (i MOD 64 + 1) = i MOD 64 + 1`
   (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`i:num`; `64`] MOD_LT_EQ) THEN ARITH_TAC);;

let BIT_OF_MOD64 = prove
 (`!x m. m < 64 ==> ((x MOD 2 EXP 64) DIV 2 EXP m) MOD 2 =
                    bitval(bit m (word(x MOD 2 EXP 64):int64))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BIT_VAL; VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  REWRITE_TAC[bitval; GSYM NOT_EVEN; MOD_2_CASES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let WORD_NEG_BITVAL = prove
 (`!b. word_neg(word(bitval b)):N word =
       if b then word_not(word 0) else word 0`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN
  REWRITE_TAC[WORD_NEG_0; WORD_NEG_1]);;

let QWORDS_BITBLAST_TAC (asl,w) =
  let bts = setify (find_terms (fun t ->
     type_of t = `:int64` &&
     can (term_match [] `word(x MOD 18446744073709551616):int64`) t) w) in
  let vs = map (fun _ -> genvar `:int64`) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let READ_MEMORY_BYTES_EQ_BITS = prove
 (`!a:int64 l n s:x86state.
        n < 2 EXP (8 * l) /\
        (!p. p < 8 * l
             ==> (bit (p MOD 8)
                   (read(memory :> bytes8(word_add a (word(p DIV 8)))) s) <=>
                  ODD(n DIV 2 EXP p)))
        ==> read(memory :> bytes(a,l)) s = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `l:num`; `n:num`; `s:x86state`]
    READ_MEMORY_BYTES_OF_BYTES8) THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_8] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `8 * j + i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(8 * j + i) MOD 8 = i /\ (8 * j + i) DIV 8 = j`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; ARITH_EQ] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_8; ODD_MOD] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM BYTE_BIT]);;

let NSUM_FIELD_BIT = prove
 (`!d c n k t.
        (!i. i < n ==> c i < 2 EXP d) /\ k < n /\ t < d
        ==> (nsum {i | i < n} (\i. c i * 2 EXP (d * i)) DIV
             2 EXP (d * k + t)) MOD 2 =
            (c k DIV 2 EXP t) MOD 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nsum {i | i < n} (\i. c i * 2 EXP (d * i)) =
    nsum {i | i < n} (\i. (2 EXP d) EXP i * c i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[EXP_EXP; IN_ELIM_THM] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; GSYM EXP_EXP] THEN
  ASM_SIMP_TAC[DIGITSUM_DIV_NUMSEG] THEN
  SUBGOAL_THEN
   `!X. (X DIV 2 EXP t) MOD 2 = ((X MOD 2 EXP d) DIV 2 EXP t) MOD 2`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`X:num`; `d:num`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
    REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n - k ==> c(i + k) < 2 EXP d` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
   [GSYM EXP_1] THEN
  ASM_SIMP_TAC[DIGITSUM_MOD_NUMSEG] THEN
  SUBGOAL_THEN `MIN (n - k) 1 = 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[num_CONV `1`; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let NSUM_FIELD_BOUND = prove
 (`!d c n. (!i. i < n ==> c i < 2 EXP d)
           ==> nsum {i | i < n} (\i. c i * 2 EXP (d * i)) < 2 EXP (d * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nsum {i | i < n} (\i. c i * 2 EXP (d * i)) =
    nsum {i | i < n} (\i. (2 EXP d) EXP i * c i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[EXP_EXP; IN_ELIM_THM] THEN
    REWRITE_TAC[MULT_SYM];
    REWRITE_TAC[GSYM EXP_EXP] THEN MATCH_MP_TAC DIGITSUM_BOUND THEN
    ASM_REWRITE_TAC[]]);;

let NSUM_BIT = prove
 (`!c n k. (!i. i < n ==> c i < 2) /\ k < n
           ==> (ODD(nsum {i | i < n} (\i. c i * 2 EXP i) DIV 2 EXP k) <=>
                c k = 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `c:num->num`; `n:num`; `k:num`; `0`] NSUM_FIELD_BIT) THEN
  ASM_REWRITE_TAC[EXP_1; MULT_CLAUSES; ADD_CLAUSES; ARITH] THEN
  REWRITE_TAC[EXP; DIV_1; ODD_MOD] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MOD_LT]);;

let WORD_CMP_BITBLAST_TAC (asl,w) =
  let cmps = ["word_ugt"; "word_ult"; "word_uge"; "word_ule";
              "word_igt"; "word_ilt"; "word_ige"; "word_ile"] in
  let is_cmp t =
    match t with
      Comb(Comb(Const(c,_),_),_) -> mem c cmps
    | _ -> false in
  let bts = setify (find_terms is_cmp w) in
  let vs = map (fun _ -> genvar bool_ty) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;

let CHUNKED_CMP_BITBLAST_TAC n (asl,w) =
  let cmps = ["word_ugt"; "word_ult"; "word_uge"; "word_ule";
              "word_igt"; "word_ilt"; "word_ige"; "word_ile"] in
  let is_cmp t =
    match t with
      Comb(Comb(Const(c,_),_),_) -> mem c cmps
    | _ -> false in
  let rec chunks l =
    if l = [] then [] else
    let a,b = chop_list (min n (length l)) l in a::chunks b in
  let prove_chunk cl =
    let t = list_mk_conj cl in
    let bts = setify (find_terms is_cmp t) in
    let vs = map (fun _ -> genvar bool_ty) bts in
    let th = BITBLAST_RULE (subst (zip vs bts) t) in
    INST (zip bts vs) th in
  let ths = map prove_chunk (chunks (conjuncts w)) in
  ACCEPT_TAC (end_itlist CONJ (flat (map CONJUNCTS ths))) (asl,w);;

let IVAL_VAL_SMALL = prove
 (`!x:int16. val x < 32768 ==> ival x = &(val x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ival; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let BIT_OF_VAL_MOD = prove
 (`!y:N word d t.
        t < d ==> ((((val y MOD 2 EXP d) DIV 2 EXP t) MOD 2 = 1) <=> bit t y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`val(y:N word)`; `d:num`; `t:num`; `1`] DIV_MOD_EXP_LOW) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_1]] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BIT_VAL; ODD_MOD]);;

let CHUNKED_ATOMS_BITBLAST_TAC n pats (asl,w) =
  let is_atom t = exists (fun p -> can (term_match [] p) t) pats in
  let rec chunks l =
    if l = [] then [] else
    let a,b = chop_list (min n (length l)) l in a::chunks b in
  let prove_chunk cl =
    let t = list_mk_conj cl in
    let bts = setify (find_terms is_atom t) in
    let vs = map (fun b -> genvar(type_of b)) bts in
    let th = BITBLAST_RULE (subst (zip vs bts) t) in
    INST (zip bts vs) th in
  let ths = map prove_chunk (chunks (conjuncts w)) in
  ACCEPT_TAC (end_itlist CONJ (flat (map CONJUNCTS ths))) (asl,w);;

let WORD_MUL_POW2 = prove
 (`!x:N word k. word_mul x (word(2 EXP k)) = word_shl x k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_SHL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_SYM]);;

let WORD_MUL_POW2_CONV =
  let rec log2 n k =
    if n = num 1 then k
    else if mod_num n (num 2) = num 0 then log2 (quo_num n (num 2)) (k + 1)
    else failwith "log2" in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_mul",_),x),Comb(Const("word",_),n))
        when is_numeral n ->
          let k = log2 (dest_numeral n) 0 in
          let th = ISPECL [x; mk_small_numeral k] WORD_MUL_POW2 in
          CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV NUM_EXP_CONV))) th
    | _ -> failwith "WORD_MUL_POW2_CONV";;

let READ_MEMORY_BYTES128_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`;
   READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let FIELD_AS_SUBWORD = prove
 (`!n p. p + dimindex(:M) <= dimindex(:N)
         ==> (n DIV 2 EXP p) MOD 2 EXP dimindex(:M) =
             val(word_subword (word n:N word) (p,dimindex(:M)):M word)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; VAL_WORD; MOD_MOD_REFL]);;

let QWORD128_AS_SUBWORD = prove
 (`!n p. p + 128 <= dimindex(:N)
         ==> word((n DIV 2 EXP p) MOD 2 EXP 128):int128 =
             word_subword (word n:N word) (p,128)`,
  SIMP_TAC[WORD_SUBWORD_WORD]);;

let LANE_ARGS_BITBLAST_TAC n pats (asl,w) =
  let cs = conjuncts w in
  let inner c = let l,r = dest_eq c in mk_eq(rand l,rand r) in
  let is_atom t = exists (fun p -> can (term_match [] p) t) pats in
  let rec chunks l =
    if l = [] then [] else
    let a,b = chop_list (min n (length l)) l in a::chunks b in
  let prove_chunk cl =
    let t = list_mk_conj (map inner cl) in
    let bts = setify (find_terms is_atom t) in
    let vs = map (fun b -> genvar(type_of b)) bts in
    let th = BITBLAST_RULE (subst (zip vs bts) t) in
    INST (zip bts vs) th in
  let iths = flat (map (CONJUNCTS o prove_chunk) (chunks cs)) in
  let oths = map2 (fun c th -> AP_TERM (rator(lhs c)) th) cs iths in
  ACCEPT_TAC (end_itlist CONJ oths) (asl,w);;

let QWORD64_AS_SUBWORD = prove
 (`!n p. p + 64 <= dimindex(:N)
         ==> word((n DIV 2 EXP p) MOD 2 EXP 64):int64 =
             word_subword (word n:N word) (p,64)`,
  SIMP_TAC[WORD_SUBWORD_WORD]);;

let READ_MEMORY_BYTES32_OF_NUM_EXP = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 4 <= m
        ==> read (memory :> bytes32(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 32)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let QWORD32_AS_SUBWORD = prove
 (`!n p. p + 32 <= dimindex(:N)
         ==> word((n DIV 2 EXP p) MOD 2 EXP 32):int32 =
             word_subword (word n:N word) (p,32)`,
  SIMP_TAC[WORD_SUBWORD_WORD]);;

(* ------------------------------------------------------------------------- *)
(* The three registers of an LD3 of bytes, as joins of the bytes of the      *)
(* 384-bit word loaded.                                                      *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBDEINTERLEAVE_3_8_GEN n =
  let mk_join ty h l =
    let cty = mk_fun_ty (type_of h) (mk_fun_ty (type_of l) ty) in
    let c = mk_const("word_join",type_match (get_const_type "word_join")
                                           cty []) in
    mk_comb(mk_comb(c,h),l) in
  let rec join_lanes tms =
    match tms with
      [t] -> t
    | _ -> let lo,hi = chop_list (length tms / 2) tms in
           mk_join (mk_word_ty(num(8 * length tms)))
                   (join_lanes hi) (join_lanes lo) in
  let xty = mk_word_ty(num(24 * n)) and rty = mk_word_ty(num(8 * n)) in
  let x = mk_var("x",xty) in
  let sw = mk_const("word_subword",
             type_match (get_const_type "word_subword")
               (mk_fun_ty xty (mk_fun_ty `:num#num` `:byte`)) []) in
  let byte k = mk_comb(mk_comb(sw,x),mk_pair(mk_small_numeral k,`8`)) in
  let sd = mk_const("word_subdeinterleave",
             type_match (get_const_type "word_subdeinterleave")
               (mk_fun_ty `:num` (mk_fun_ty `:num` (mk_fun_ty xty
                 (mk_fun_ty `:num` rty)))) []) in
  let clause j =
    mk_eq(list_mk_comb(sd,[`3`; `8`; x; mk_small_numeral j]),
          join_lanes (map (fun m -> byte(24 * m + 8 * j)) (0--(n-1)))) in
  prove
   (mk_forall(x,list_mk_conj (map clause [0;1;2])),
    GEN_TAC THEN REPEAT CONJ_TAC THEN
    GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN
    REWRITE_TAC[word_subdeinterleave; BIT_WORD_OF_BITS; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[]);;

let WORD_SUBDEINTERLEAVE_3_8 = WORD_SUBDEINTERLEAVE_3_8_GEN 16;;

let WORD_SUBDEINTERLEAVE_3_8_64 = WORD_SUBDEINTERLEAVE_3_8_GEN 8;;

(* ------------------------------------------------------------------------- *)
(* A subword starting beyond the top of a word is 0, as for the out-of-range *)
(* indices of a table lookup.                                                *)
(* ------------------------------------------------------------------------- *)

let WORD_SUBWORD_BEYOND = prove
 (`!x:N word p l. dimindex(:N) <= p ==> word_subword x (p,l):M word = word 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val(x:N word) DIV 2 EXP p = 0`
   (fun th -> REWRITE_TAC[th; MOD_0]) THEN
  MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP dimindex(:N)` THEN
  ASM_REWRITE_TAC[VAL_BOUND; LE_EXP; ARITH_EQ]);;

let WORD_SUBWORD_BEYOND_CONV tm =
  match tm with
    Comb(Comb(Const("word_subword",_),x),Comb(Comb(Const(",",_),p),l))
      when is_numeral p ->
        let th = PART_MATCH (lhand o rand) WORD_SUBWORD_BEYOND tm in
        let c = lhand(concl th) in
        let cth = (LAND_CONV DIMINDEX_CONV THENC NUM_LE_CONV) c in
        if rand(concl cth) = `T` then MP th (EQT_ELIM cth)
        else failwith "WORD_SUBWORD_BEYOND_CONV"
  | _ -> failwith "WORD_SUBWORD_BEYOND_CONV";;

(* ------------------------------------------------------------------------- *)
(* Further lemmas for the x86 leaves: 16-bit loads of the bytes of a number, *)
(* and bits of a number as bits of a word.                                   *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES16_OF_NUM_EXP = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 2 <= m
        ==> read (memory :> bytes16(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 16)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WORD16_AS_SUBWORD = prove
 (`!n p. p + 16 <= dimindex(:N)
         ==> word((n DIV 2 EXP p) MOD 2 EXP 16):int16 =
             word_subword (word n:N word) (p,16)`,
  SIMP_TAC[WORD_SUBWORD_WORD]);;

let NUM_BIT_AS_WORD_BIT = prove
 (`!n i. i < dimindex(:N)
         ==> (n DIV 2 EXP i) MOD 2 = bitval(bit i (word n:N word))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[BIT_WORD; bitval] THEN
  REWRITE_TAC[GSYM NOT_EVEN; MOD_2_CASES] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;
