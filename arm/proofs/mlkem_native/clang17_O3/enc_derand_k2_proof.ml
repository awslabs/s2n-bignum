(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/enc_derand_k2_spec.ml";;


let MLKEM_EK_CHECK_512 = prove
 (MLKEM_EK_CHECK_512_STMT,
  SIMP_TAC[mlkem512; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

let KE2_CHECK_EQ = prove
 (KE2_CHECK_EQ_STMT,
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DIV_MOD_EXP_LOW THEN ASM_ARITH_TAC);;

let KE2_BUFFER_ADDRESS = prove
 (KE2_BUFFER_ADDRESS_STMT,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(* ----- lemmas and tactics for the comparison, as for mlkem512_check_pk ----- *)

let KE2_BYTES16_LIST = prove
 (`!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let KE2_IVAL_WORD = prove
 (`!f. f < 32768 ==> ival(word f:int16) = &f`,
REPEAT STRIP_TAC THEN REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 32768 ==> f < 65536`]);;

let KE2_REDUCED = prove
 (`!(x:int16) f.
        f < 2 EXP 12 /\ ival x = ival(word f:int16) rem &3329
        ==> x = word(f MOD 3329)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word f:int16) = &f` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC KE2_IVAL_WORD THEN UNDISCH_TAC `f < 2 EXP 12` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_REM]) THEN
  ONCE_REWRITE_TAC[GSYM IVAL_EQ] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC KE2_IVAL_WORD THEN
  MP_TAC(SPECL [`f:num`; `3329`] MOD_LT_EQ) THEN ARITH_TAC);;

let KE2_LIST_PROPS = prove
 (`!(g:num->num) l.
        LENGTH(list_of_seq (\i. word(g i MOD 3329):int16) l) = l /\
        ALL (\x. val x < 4096) (list_of_seq (\i. word(g i MOD 3329):int16) l)`,
REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ; VAL_WORD; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`(g:num->num) i`; `3329`] MOD_LT_EQ) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x < 3329 ==> x < 65536`] THEN ARITH_TAC);;

let KE2_REENCODE = prove
 (`!l n. n < 2 EXP (12 * l)
         ==> (n = num_of_wordlist(MAP (word_zx:int16->12 word)
                    (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD
                                            2 EXP 12) MOD 3329):int16) l)) <=>
              !i. i < l ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
REPEAT STRIP_TAC THEN REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  SUBGOAL_THEN
   `!x. word_zx(word(x MOD 3329):int16):12 word = word(x MOD 3329)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ARITH_RULE `x MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 65536`];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`; LENGTH_LIST_OF_SEQ]
     (ISPECL [`list_of_seq (\x. word((n DIV 2 EXP (12 * x)) MOD 2 EXP 12 MOD
                                     3329):12 word) l`; `i:num`]
             NUM_OF_WORDLIST_EL)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
    ASM_SIMP_TAC[EL_LIST_OF_SEQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    SPEC_TAC(`(n DIV 2 EXP (12 * i)) MOD 4096`,`d:num`) THEN GEN_TAC THEN
    MP_TAC(ARITH_RULE `d MOD 3329 < 3329`) THEN
    SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4096`] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[DIMINDEX_CONV `dimindex(:12)`]
    (ISPECL [`l:num`; `n:num`]
      (INST_TYPE [`:12`,`:N`] NUM_OF_WORDLIST_OF_NUM_EQ_SELF))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th] THEN
                       ASSUME_TAC th) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_WORDLIST_OF_NUM; LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[EL_LIST_OF_SEQ] THEN
  MP_TAC(ISPECL [`wordlist_of_num l n:(12 word)list`; `i:num`]
                EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; MOD_MOD_REFL]);;

let KE2_BYTES128 = prove
 (`!a l k n s:armstate.
        read (memory :> bytes(a,l)) s = n /\ 16 * k + 16 <= l
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word((n DIV 2 EXP (128 * k)) MOD 2 EXP 128)`,
REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `128 * k = 8 * 16 * k`; READ_BYTES_DIV] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_MOD; MOD_MOD_REFL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let KE2_MOD_STEP = prove
 (`!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`,
REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * (k + 1) = 128 * k + 128`; EXP_ADD] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEXICOGRAPHIC_EQ o lhand o snd) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

let KE2_MOD_ALL = prove
 (`!n m k. n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) <=>
          !j. j < k ==> (n DIV 2 EXP (128 * j)) MOD 2 EXP 128 =
                        (m DIV 2 EXP (128 * j)) MOD 2 EXP 128`,
REPEAT GEN_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; LT]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC k = k + 1`] THEN
  ASM_REWRITE_TAC[KE2_MOD_STEP] THEN
  REWRITE_TAC[ARITH_RULE `!j. j < k + 1 <=> j < k \/ j = k`] THEN
  MESON_TAC[]);;

let KE2_DREG = prove
 (`!x:int64. word_zx(word_zx x:int128):int64 = x`,
  BITBLAST_TAC);;

let KE2_M =
 `num_of_wordlist(MAP (word_zx:int16->12 word)
   (list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329))
                512))`;;

let KE2_BOUND a s =
  REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
   (ISPECL [a; `768`; mk_comb(`read memory:armstate->int64->byte`,s)]
           READ_BYTES_BOUND);;

let KE2_CHUNK_TAC norm a v k =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),Comb(_,Comb(Const("bytes",_),aa))),
                     s)),vv)
        when aa = mk_pair(a,`768`) && vv = v ->
          let kt = mk_small_numeral k in
          let bth = EQT_ELIM(NUM_REDUCE_CONV (subst [kt,`k:num`]
                      `16 * k + 16 <= 768`)) in
          let lth = SPECL [a; `768`; kt; v; s] KE2_BYTES128 in
          let fth = MP lth (CONJ th bth) in
          let fth = CONV_RULE (DEPTH_CONV NUM_MULT_CONV) fth in
          let fth = REWRITE_RULE[WORD_ADD_0] fth in
          ASSUME_TAC(if norm then CONV_RULE(ONCE_DEPTH_CONV
                                    NORMALIZE_RELATIVE_ADDRESS_CONV) fth
                     else fth)
    | _ -> NO_TAC);;

let KE2_EXP_THS =
  NUM_REDUCE_CONV `2 EXP 128` ::
  map (fun k -> NUM_REDUCE_CONV (subst [mk_small_numeral k,`k:num`]
                                  `2 EXP (128 * k)`)) (0--47);;

let KE2_ABBREV_TAC reg nm var =
  W(fun (asl,w) ->
    let big = rhs(concl(snd(find (fun (_,th) ->
      let c = concl th in
      is_eq c &&
      (let l = lhs c in
       (try fst(dest_const(rator(rator l))) = "read" with Failure _ -> false) &&
       rand(rator l) = reg && rand l = mk_var(nm,`:armstate`))) asl))) in
    ABBREV_TAC(mk_eq(mk_var(var,`:int128`),big)));;

let KE2_CHUNK_IFF_TAC =
  REWRITE_TAC[KE2_MOD_ALL] THEN
  CONV_TAC(RAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  REWRITE_TAC KE2_EXP_THS THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  EQ_TAC THEN DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC ths));;

let KE2_CLEAN_TAC =
  DISCARD_ASSUMPTIONS_TAC(fun th ->
    let c = concl th in
    (is_eq c && (rand c = `q9:int128` || rand c = `q0:int128`) &&
     not(is_var(lhand c)) &&
     not(try fst(dest_const(rator(rator(lhand c)))) = "read"
         with Failure _ -> false)) ||
    (is_iff c && lhand c = `q9:int128 = word 0` &&
     not(is_forall(rand c))) ||
    can (term_match [] `read (memory :> bytes128 a) s = x`) c);;

let KE2_EV_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let KE2_EV_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE KE2_EV_CONV th else th);;

let KE2_PRESERVE_TAC =
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)];;


let ke2_bsub b tm = vsubst [mk_small_numeral b,`boff:num`] tm;;

let KE2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KE2_BUFFER_ADDRESS))
    else NO_TAC);;

let KE2_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_256_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KE2_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KE2_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KE2_FROMBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;
let KE2_REDUCE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;
let KE2_TOBYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT);;

let KE2_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP b in
  let gt = `sha3_512 (APPEND (m:byte list) (sha3_256 ek))` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; gt; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; gt; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek))))
    = 32 /\
    LENGTH(mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek)))) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KE2_FINAL_TAC =
  REWRITE_TAC[mlkem512; MLKEM_ENCAPS_PAIR] THEN REWRITE_TAC[GSYM mlkem512] THEN
  ASM_REWRITE_TAC[];;

let KE2_L =
 `list_of_seq (\i. word(((n DIV 2 EXP (12 * i)) MOD 2 EXP 12) MOD 3329):int16)
              512`;;

let KE2_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let KE2_CHECK = `!i. i < 512 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`;;

let KE2_N_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,800)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 800 768 = 768`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 768)`)))
    else NO_TAC);;

let KE2_FIX_N_TAC =
  FIRST_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `n:num` &&
       not(is_var(lhand(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC);;

let KE2_HM_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 768),`a:int64`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (m:byte list) (sha3_256 ek))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(APPEND (m:byte list) (sha3_256 ek)) = 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SHA3_256] THEN ARITH_TAC;
    ALL_TAC];;

let KE2_LIST_TAC b s =
  let p = string_of_int (b + 768) in
  SUBGOAL_THEN (vsubst [s,`s:armstate`]
   (parse_term ("read (memory :> bytes(word_add stackpointer (word " ^ p ^ "),1024)) s =
    num_of_wordlist(list_of_seq (\\i. word(((n DIV 2 EXP (12 * i)) MOD
                                           2 EXP 12) MOD 3329):int16) 512)")))
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 2 * 512`] THEN
    MATCH_MP_TAC KE2_BYTES16_LIST THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC KE2_REDUCED THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN
     (parse_term ("word_add (word_add stackpointer (word " ^ p ^ "))
               (word (2 * i)):int64 =
       word_add stackpointer (word (" ^ p ^ " + 2 * i))"))
     (fun th -> REWRITE_TAC[th]) THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let KE2_PART1_TAC b =
  ENSURES_INIT_TAC "s0" THEN KE2_N_TAC THEN KE2_FIX_N_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (1--13) THEN KE2_BUFFER_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (14--14) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (15--25) THEN
  KE2_FROMBYTES_TAC [`read X0 s`; `read X1 s`; `n:num`;
                     `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC KE2_EXEC (27--28) THEN
  KE2_REDUCE_TAC [`read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  KE2_LIST_TAC b `s29:armstate` THEN KE2_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (30--33) THEN
  KE2_TOBYTES_TAC [`read X0 s`; `read X1 s`; KE2_L;
                   `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KE2_LIST_PROPS]);;

let KE2_IFF_TAC b s =
  SUBGOAL_THEN
   `q9:int128 = word 0 <=>
    n MOD 2 EXP (128 * 48) = mm MOD 2 EXP (128 * 48)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) && rand(concl th) = `q9:int128`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    KE2_CHUNK_IFF_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `q9:int128 = word 0 <=>
    !i. i < 512 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0`
      then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC(KE2_BOUND `pk:int64` s) THEN
    MP_TAC(KE2_BOUND (ke2_bsub b `word_add stackpointer (word boff):int64`) s) THEN
    ASM_REWRITE_TAC[ARITH_RULE `8 * 768 = 128 * 48`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = mk_eq(KE2_M,`mm:num`))) THEN
    MATCH_MP_TAC KE2_REENCODE THEN
    ASM_REWRITE_TAC[ARITH_RULE `12 * 512 = 128 * 48`];
    ALL_TAC];;

let KE2_COMPARE_TAC b =
  ABBREV_TAC(mk_eq(`mm:num`,KE2_M)) THEN
  MAP_EVERY (fun k -> KE2_CHUNK_TAC false `pk:int64` `n:num` k) (0--47) THEN
  MAP_EVERY (fun k ->
    KE2_CHUNK_TAC true (ke2_bsub b `word_add stackpointer (word boff):int64`) `mm:num` k)
    (0--47) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (35--221) THEN
  KE2_ABBREV_TAC `Q9` "s221" "q9" THEN
  KE2_IFF_TAC b `s221:armstate` THEN
  KE2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (222--230) THEN
  KE2_ABBREV_TAC `Q0` "s230" "q0" THEN
  KE2_CLEAN_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC KE2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (231--245);;

let KE2_MEMSET_TAC =
  ARM_STEPS_TAC KE2_EXEC (246--246) THEN
  LIBC_PLT_TAC KE2_EXEC 246 THEN
  LIBC_CALL_TAC "H_MEMSET" KE2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 251 THEN
  ARM_STEPS_TAC KE2_EXEC (252--255) THEN
  LIBC_PLT_TAC KE2_EXEC 255 THEN
  LIBC_CALL_TAC "H_MEMSET" KE2_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 260 THEN
  ARM_STEPS_TAC KE2_EXEC (261--262);;

let KE2_JOIN_TAC a l s =
  MP_TAC(SPECL [a; mk_comb(`num_of_bytelist`,l);
                mk_var(s,`:armstate`)] KEM_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPEC l NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC];;

let KE2_REST_PASS_TAC b =
  KEM_HALVES_TAC `coins:int64` THEN
  ARM_STEPS_TAC KE2_EXEC (263--268) THEN
  KE2_JOIN_TAC (KEM_SP(b + 768)) `m:byte list` "s268" THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 269 THEN
  KE2_HM_TAC b "s269" THEN
  ARM_STEPS_TAC KE2_EXEC (270--273) THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND (m:byte list) (sha3_256 ek)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 274 THEN
  KE2_KR_TAC b "s274" THEN
  KEM_HALVES_TAC (KEM_SP b) THEN
  ARM_STEPS_TAC KE2_EXEC (275--279) THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
    `m:byte list`;
    `mlkem_slice 32 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 280 THEN
  ARM_STEPS_TAC KE2_EXEC (281--292) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (293--309) THEN
  KE2_JOIN_TAC `ss:int64`
   `mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`
   "s309" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KE2_DREG] THEN KE2_FINAL_TAC;;

let KE2_REST_FAIL_TAC b =
  ARM_STEPS_TAC KE2_EXEC (263--271) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (272--288) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KE2_DREG];;

let KE2_IFF_FIND f =
  FIRST_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `q9:int128 = word 0` && rand(concl th) = KE2_CHECK then f th else NO_TAC);;

let KE2_PCFIX_TAC case =
  FIRST_X_ASSUM(fun th ->
    if (try lhand(concl th) = `read PC s262` with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[ASSUME case] th) else NO_TAC);;

let KE2_BRANCH2_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = try (fun (c,_) -> c) (dest_cond(rand(concl th)))
            with Failure _ -> failwith "no cond" in
    if lhand(concl th) <> `read PC s262` then failwith "not s262" else
    SUBGOAL_THEN
     (mk_eq(c,`~(q9:int128 = word 0)`))
     (fun eqth -> ASSUME_TAC(REWRITE_RULE[eqth] th)) THENL
     [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC]);;

let KE2_BRANCH_TAC b =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `num_of_bytelist ek MOD 2 EXP (8 * 768) = n`); KE2_CHECK_EQ]) THEN
  KE2_BRANCH2_TAC THEN
  ASM_CASES_TAC `q9:int128 = word 0` THENL
   [SUBGOAL_THEN KE2_CHECK ASSUME_TAC THENL
     [KE2_IFF_FIND (fun th -> ACCEPT_TAC(EQ_MP th (ASSUME `q9:int128 = word 0`)));
      ALL_TAC] THEN
    KE2_PCFIX_TAC `q9:int128 = word 0` THEN
    KE2_REST_PASS_TAC b;
    SUBGOAL_THEN (mk_neg KE2_CHECK) ASSUME_TAC THENL
     [KE2_IFF_FIND (fun th -> REWRITE_TAC[GSYM th] THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    KE2_PCFIX_TAC `~(q9:int128 = word 0)` THEN
    KE2_REST_FAIL_TAC b];;

let KE2_PRE_TAC b =
  SUBGOAL_THEN (ke2_bsub b `aligned 16 (word_add stackpointer (word boff):int64)`)
   ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (stackpointer:int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    CONV_TAC(RAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = num_of_bytelist ek MOD 2 EXP (8 * 768)`;;

let KE2_CASE_TAC b =
  KE2_PRE_TAC b THEN KE2_PART1_TAC b THEN KE2_COMPARE_TAC b THEN
  KE2_MEMSET_TAC THEN KE2_BRANCH_TAC b;;

let KE2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 13792 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `memset_contract mf ea el ev`) (concl th)
    then LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th)
    else NO_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13792):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_512; ASSUME `LENGTH(ek:byte list) = 800`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  KE2_PRESERVE_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  KE2_INTRO_TAC THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [KE2_CASE_TAC 11808; KE2_CASE_TAC 11792]);;

let KE2_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (guard:int64)
   (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list).
   if aligned 32 stackpointer
   then (if mlkem_ek_check mlkem512 ek
         then f_ev_a1 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek
         else f_ev_a0 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek)
   else (if mlkem_ek_check mlkem512 ek
         then f_ev_u1 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek
         else f_ev_u0 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek)
   :(uarch_event)list`;;

let KE2_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ek:byte list`];;

let KE2_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_INDCPA" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (REWRITE_RULE[memset_safety_contract]
         (CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1))) "H_MEMSET")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_FROMBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_FROMBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_REDUCE_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_REDUCE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLYVEC_TOBYTES_K2_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_TOBYTES" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_256_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHA3_256" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  CONCRETIZE_F_EVENTS_TAC KE2_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 13792):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_512; ASSUME `LENGTH(ek:byte list) = 800`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--29) THEN
  KE2_PRESERVE_TAC;;

let KE2_SAFE_CALL_TAC name ilist n =
  KE2_NORMALIZE_TAC THEN
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,KE2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KE2_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KE2_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [CONV_TAC(RAND_CONV KE2_EV_CONV) THEN FULL_UNIFY_F_EVENTS_TAC;
    ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let KE2_SAFE_PART1_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  KE2_N_TAC THEN KE2_FIX_N_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (1--13) THEN KE2_BUFFER_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (14--14) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (15--25) THEN
  KE2_SAFE_CALL_TAC "H_FROMBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `n:num`;
    `pc:num`; `read SP s`; `read X30 s`] 26 THEN
  ARM_STEPS_TAC KE2_EXEC (27--28) THEN
  KE2_SAFE_CALL_TAC "H_REDUCE"
   [`e:(uarch_event)list`; `read X0 s`;
    `\i. word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12):int16`;
    `pc:num`; `read SP s`; `read X30 s`] 29 THEN
  KE2_LIST_TAC b `s29:armstate` THEN KE2_NORMALIZE_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (30--33) THEN
  KE2_SAFE_CALL_TAC "H_TOBYTES"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; KE2_L;
    `pc:num`; `read SP s`; `read X30 s`] 34 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KE2_LIST_PROPS]);;

let KE2_SAFE_MEMSET_TAC =
  ARM_STEPS_TAC KE2_EXEC (246--246) THEN
  LIBC_PLT_TAC KE2_EXEC 246 THEN
  KE2_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KE2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KE2_SAFE_ALLOWED) 251 THEN
  ARM_STEPS_TAC KE2_EXEC (252--255) THEN
  LIBC_PLT_TAC KE2_EXEC 255 THEN
  KE2_EV_NORMALIZE_TAC THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KE2_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KE2_SAFE_ALLOWED) 260 THEN
  ARM_STEPS_TAC KE2_EXEC (261--262);;

let KE2_SAFE_PASS_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`] in
  ARM_STEPS_TAC KE2_EXEC (263--268) THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_SAFE_CALL_TAC "H_SHA3_256" ([e; x 0; x 1; `800`] @ rest) 269 THEN
  ARM_STEPS_TAC KE2_EXEC (270--273) THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_SAFE_CALL_TAC "H_SHA3_512" ([e; x 0; x 1; `64`] @ rest) 274 THEN
  ARM_STEPS_TAC KE2_EXEC (275--279) THEN
  KE2_NORMALIZE_TAC THEN KEM_GOT_TAC THEN
  KE2_SAFE_CALL_TAC "H_INDCPA"
   ([e; x 0; x 1; x 2; x 3; `ek:byte list`] @ rest) 280 THEN
  ARM_STEPS_TAC KE2_EXEC (281--292) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (293--309) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KE2_DREG] THEN
  KE2_DISCHARGE_TAC;;

let KE2_SAFE_FAIL_TAC b =
  ARM_STEPS_TAC KE2_EXEC (263--271) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE2_EXEC (272--288) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[KE2_DREG] THEN
  KE2_DISCHARGE_TAC;;

(* variants that rewrite the events as well as the PC *)
let KE2_BRANCH2_EV_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = try (fun (c,_) -> c) (dest_cond(rand(concl th)))
            with Failure _ -> failwith "no cond" in
    if lhand(concl th) <> `read PC s262` then failwith "not s262" else
    SUBGOAL_THEN
     (mk_eq(c,`~(q9:int128 = word 0)`))
     (fun eqth -> ASSUME_TAC(REWRITE_RULE[eqth] th) THEN
                  RULE_ASSUM_TAC(fun h ->
                    if try lhand(concl h) = `read events s262` with Failure _ -> false
                    then REWRITE_RULE[eqth] h else h)) THENL
     [W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)); ALL_TAC]);;

let KE2_PCFIX_EV_TAC case =
  RULE_ASSUM_TAC(fun th ->
    if (try lhand(concl th) = `read PC s262` || lhand(concl th) = `read events s262` with Failure _ -> false)
    then REWRITE_RULE[ASSUME case] th else th);;

let KE2_SAFE_BRANCH_TAC b =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `num_of_bytelist ek MOD 2 EXP (8 * 768) = n`); KE2_CHECK_EQ]) THEN
  KE2_BRANCH2_EV_TAC THEN
  ASM_CASES_TAC `q9:int128 = word 0` THENL
   [SUBGOAL_THEN KE2_CHECK ASSUME_TAC THENL
     [KE2_IFF_FIND (fun th -> ACCEPT_TAC(EQ_MP th (ASSUME `q9:int128 = word 0`)));
      ALL_TAC] THEN
    KE2_PCFIX_EV_TAC `q9:int128 = word 0` THEN
    KE2_SAFE_PASS_TAC b;
    SUBGOAL_THEN (mk_neg KE2_CHECK) ASSUME_TAC THENL
     [KE2_IFF_FIND (fun th -> REWRITE_TAC[GSYM th] THEN FIRST_ASSUM ACCEPT_TAC);
      ALL_TAC] THEN
    KE2_PCFIX_EV_TAC `~(q9:int128 = word 0)` THEN
    KE2_SAFE_FAIL_TAC b];;

let KE2_SAFE_CASE_TAC b =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then REWRITE_TAC[th] else NO_TAC) THEN
  KE2_PRE_TAC b THEN KE2_SAFE_PART1_TAC b THEN KE2_COMPARE_TAC b THEN
  KE2_SAFE_MEMSET_TAC THEN KE2_SAFE_BRANCH_TAC b;;

let MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_ENC_DERAND_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  KE2_SAFE_INTRO_TAC THEN
  PAR_THENL (ASM_CASES_TAC `aligned 32 (stackpointer:int64)`)
   [KE2_SAFE_CASE_TAC 11808; KE2_SAFE_CASE_TAC 11792]);;
