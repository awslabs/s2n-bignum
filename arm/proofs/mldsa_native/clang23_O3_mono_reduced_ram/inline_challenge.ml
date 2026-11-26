(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa{44,65,87}_poly_challenge of    *)
(* the clang 23 -O3 build (see poly_challenge_*_spec.ml). Clang inlined the  *)
(* SHAKE256 functions: the code XORs the seed and the padding into a zeroed  *)
(* Keccak state on the stack with straight-line vector code, copies the      *)
(* first block of 136 bytes of the permuted state to a buffer with 128-bit   *)
(* loads and stores, and reads the bytes of the buffer in a loop that        *)
(* calls mldsa_keccakf1600_permute and copies the next block when the        *)
(* buffer is used up. The tools here are those of the proofs of poly_uniform *)
(* (the facts about the pieces of the state and the bytes of the seed that   *)
(* the simulator does not derive from the 1600-bit state) and of the         *)
(* challenge polynomial (utils/mldsa_native_challenge.ml).                   *)
(* ========================================================================= *)


needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_challenge.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(*** The bytes of a seed of n bytes as subwords of word C : (8n) word ***)

let PC_BYTE_SUB n = prove
 (parse_term(Printf.sprintf "!C j. C < 2 EXP %d
         ==> word((C DIV 2 EXP (8 * j)) MOD 256):byte =
             word_subword (word C:%d word) (8 * j,8)" (8*n) (8*n)),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  REWRITE_TAC[MIN; LE_REFL; MOD_MOD_REFL; ARITH_RULE `2 EXP 8 = 256`]);;

let PC_SEED_HYP n = parse_term
  (Printf.sprintf "!j. j < %d ==> read (memory :> bytes8 (word_add seed (word j))) s0 = word_subword (word C:%d word) (8 * j,8)" n (8*n));;

let PC_SEED_FACT n sz k =
  let hth = ASSUME (PC_SEED_HYP n) in
  let insts = map (fun i ->
    let j = k + i in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,mk_small_numeral n)))) in
    CONV_RULE(DEPTH_CONV NUM_RED_CONV) (REWRITE_RULE[WORD_ADD_0] th)) (0--(sz-1)) in
  let addr = if k = 0 then "seed" else Printf.sprintf "word_add seed (word %d)" k in
  let lhs = parse_term(Printf.sprintf "read (memory :> bytes%d (%s)) s0" (8 * sz) addr) in
  let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          PTR_ADD_G; GSYM ADD_ASSOC] THENC
             DEPTH_CONV NUM_ADD_CONV in
  let th = conv lhs in
  let th2 = REWRITE_RULE (WORD_ADD_0 :: insts) th in
  DISCH (PC_SEED_HYP n) th2;;

let PC_SEED_BYTE n j = ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV) (MP (SPEC (mk_small_numeral j) (ASSUME (PC_SEED_HYP n))) (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,mk_small_numeral n))))));;

let PC_UNSPLIT = CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT @ [PTR_ADD_G; GSYM ADD_ASSOC; WORD_ADD_0];;
let PC_ZSPLIT sname off =
  let s = mk_var(sname,`:armstate`) in
  let tm = subst [s,`s0:armstate`; mk_small_numeral off,`OFF:num`]
    `read (memory :> bytes128 (word_add sp (word OFF))) s0 = word 0:int128` in
  FIRST_ASSUM(fun th ->
    if concl th = tm then
      let th1 = REWRITE_RULE PC_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let ths = map (CONV_RULE(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC ths
    else NO_TAC);;
let PC_ZLD_TAC sname sz k =
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add sp (word %d))) %s = word 0" (8*sz) k sname) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

let READ_MEMORY_BYTES_EXTEND = prove
 (`!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let PU_B16 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
let PU_B1 = prove(`!a:int64 s:armstate. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;

let PU_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_B16] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let PU_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:armstate) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_B1] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PC_NORMC = TRY_CONV(REWRITE_CONV[PTR_ADD_G]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let PC_NORM = CONV_RULE PC_NORMC;;

(* the state word: seed C of n bytes, 0x1F after it, 0x80 at byte 135 *)
let PC_SW n = parse_term(Printf.sprintf "word_or (word_zx (word C:%d word):1600 word) (word(2 EXP %d * 31 + 2 EXP 1080 * 128))" (8*n) (8*n));;

(* the piece of length len at offset off from sp + 16 at the state sn *)
let PC_PIECE_THM sw asl sn off len =
  let sz,lem = if len = 16 then "bytes128",PU_PIECE16 else "bytes8",PU_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add sp (word %d))) %s" sz (16 + off) sn) in
  let fact = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add sp (word %d):int64" (16 + off)) in
  let s = mk_var(sn,`:armstate`) in
  let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

(* bytes(sp+16,200) = val sw at the state sn, as a chain of extensions *)
let PC_CHAIN_TAC n pieces sn =
  W(fun (asl,w) ->
    let sw = PC_SW n in
    let s = mk_var(sn,`:armstate`) in
    let d = `word_add sp (word 16):int64` in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = PC_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`]
       `read (memory :> bytes(word_add sp (word 16),0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = PC_NORM(PC_PIECE_THM sw asl sn off len) in
      let ext = PC_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) pieces (cur0,0) in
    ASSUME_TAC fin);;

(*** The state after absorbing n < 135 bytes and finalizing, as a word ***)

let PC_STATE_WORD n =
  let b = 8 * n in
  prove(parse_term(Printf.sprintf "!C. C < 2 EXP %d
         ==> mld_shake256_state %d C =
             word_or (word_zx (word C:%d word):1600 word) (word(2 EXP %d * 31 + 2 EXP 1080 * 128))" b n b b),
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "word C:1600 word = word_zx (word C:%d word)" b)) ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV (parse_term(Printf.sprintf "dimindex(:%d)" b))] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "C < 2 EXP 1600")) ASSUME_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (parse_term(Printf.sprintf "2 EXP %d" b)) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE (parse_term(Printf.sprintf "MIN %d 1600 = %d" b b))] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mld_shake256_state; mld_keccak_absorb; mld_keccak_finalize] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; ARITH_RULE (parse_term(Printf.sprintf "%d < 136" n))] THEN
  REWRITE_TAC[mld_keccak_absorb_blocks; MULT_CLAUSES; ADD_CLAUSES; EXP; DIV_1; WORD_XOR_0] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "C MOD 2 EXP (8 * 136) = C")) SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC (parse_term(Printf.sprintf "2 EXP %d" b)) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(*** Reading 8 and 16 bytes of an array given as a number ***)

let READ_MEMORY_BYTES64_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
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

let READ_MEMORY_BYTES128_OF_NUM = prove
 (`!a:int64 m n k s:armstate.
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

(* PC_LOAD_FACTS_TAC base sname ks: for the bytes(base,200) = X fact at the *)
(* state sname, the facts for the loads of sizes 16 and 8 at offsets ks.    *)
let PC_LOAD_FACTS_TAC base sname ks =
  let btm = parse_term ("(" ^ base ^ "):int64") in
  let sv = mk_var(sname,`:armstate`) in
  let pat = subst [sv,`s:armstate`; btm,`a:int64`]
    `read (memory :> bytes(a,200)) s` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = pat then
      MAP_EVERY (fun (sz,k) ->
        let lem = if sz = 16 then READ_MEMORY_BYTES128_OF_NUM else READ_MEMORY_BYTES64_OF_NUM in
        let kt = mk_small_numeral k in
        let ar = EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<=" (mk_binary "+" (kt,mk_small_numeral sz),`200`))) in
        let inst = MP (SPECL [btm; `200`; rhs c; kt; sv] lem) (CONJ th ar) in
        ASSUME_TAC(CONV_RULE PC_NORMC inst)) ks
    else NO_TAC);;

(* the low 64 bits of a 128-bit fact at addr (a term string) at state sname *)
let PC_SPLIT64_TAC addr sname =
  let a = parse_term ("(" ^ addr ^ "):int64") in
  let s = mk_var(sname,`:armstate`) in
  let pat = subst [a,`x:int64`; s,`s:armstate`] `read (memory :> bytes128 x) s` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhs c = pat then
      ASSUME_TAC(CONJUNCT1(REWRITE_RULE[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] th))
    else NO_TAC);;

(* libc call whose events are unified as in poly_uniform *)
let PC_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let PC_E2_CORE allowed =
    CONV_TAC(LAND_CONV PC_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let PC_E2_TAC allowed =
  (CONJ_TAC THENL [FIRST [REFL_TAC; CONV_TAC WORD_RULE; ASM_REWRITE_TAC[] THEN NO_TAC]; PC_E2_CORE allowed]) ORELSE PC_E2_CORE allowed;;
let PC_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [PC_E2_TAC (ref vars); LABEL_TAC name th]);;

(*** Pieces of a number read as 128-bit and 64-bit words ***)

let PC_PIECE128 = prove
 (`!A:int64 s:armstate x off.
     read (memory :> bytes128 A) s = word((x DIV 2 EXP off) MOD 2 EXP 128)
     ==> read (memory :> bytes(A,16)) s = (x DIV 2 EXP off) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_B16] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_CONV `dimindex(:128)`] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;
let PC_PIECE64 = prove
 (`!A:int64 s:armstate x off.
     read (memory :> bytes64 A) s = word((x DIV 2 EXP off) MOD 2 EXP 64)
     ==> read (memory :> bytes(A,8)) s = (x DIV 2 EXP off) MOD 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[BYTES64_WBYTES; READ_COMPONENT_COMPOSE]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_64; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

(* chain: bytes(addr 0, len) at state sname = x MOD 2^(8 len), from the facts
   for the pieces (off,len) at addr off, with x the number xtm *)
let PC_CHAIN_GEN base basevar boff xtm sname pieces =
  W(fun (asl,w) ->
    let s = mk_var(sname,`:armstate`) in
    let x = parse_term xtm in
    let addr off = parse_term(Printf.sprintf "word_add %s (word %d):int64" basevar (boff + off)) in
    let d = addr 0 in
    let cur0 = PC_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let a = addr off in
      let lem = if len = 16 then PC_PIECE128 else PC_PIECE64 in
      let inst = SPECL [a; s; x; mk_small_numeral (8 * off)] lem in
      let ante = fst(dest_imp(concl inst)) in
      let nante = DEPTH_CONV NUM_RED_CONV ante in
      let fact0 = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = lhs ante) asl) in
      let fact = CONV_RULE(DEPTH_CONV NUM_RED_CONV) fact0 in
      let pth = PC_NORM(MP inst (EQ_MP (SYM nante) fact)) in
      let ext = PC_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) pieces (cur0,0) in
    ASSUME_TAC fin);;

let PC_SIGNS = prove
 (`!x. word_subword (word((x DIV 1) MOD 2 EXP 128):int128) (0,64):int64 = word(x MOD 2 EXP 64)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_CONV `dimindex(:128)`; DIMINDEX_CONV `dimindex(:64)`] THEN
  REWRITE_TAC[DIV_1; MOD_MOD_REFL; EXP; MOD_MOD_EXP_MIN; ARITH_RULE `MIN 128 64 = 64`; ARITH_RULE `MIN 64 64 = 64`] THEN
  REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`; ARITH_RULE `MIN 128 64 = 64`]);;

let PC_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** i bytes of block b of the SHAKE256 output as a number ***)

let PC_BLOCK = prove
 (`!inlen M b i. i <= 136
     ==> num_of_bytelist(list_of_seq (\t. mld_shake256_byte inlen M (136 * b + t)) i) =
         val(keccak_squeeze (b + 1) (mld_shake256_state inlen M)) MOD 2 EXP (8 * i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`136`; `mld_shake256_state inlen M`; `136`; `136 * b`; `b + 1`; `0`; `i:num`] SQUEEZE_CHUNK) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[mld_shake256_byte; ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1]);;

let PC_BLOCK0 = prove
 (`!inlen M i. i <= 136
     ==> num_of_bytelist(list_of_seq (mld_shake256_byte inlen M) i) =
         val(keccak_squeeze 1 (mld_shake256_state inlen M)) MOD 2 EXP (8 * i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlen:num`; `M:num`; `0`; `i:num`] PC_BLOCK) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX]);;


let PC_UXTB = prove
 (`!m. m < 256 ==> val(word_zx(word_zx(word_zx(word m:int64):int32):byte):int32) = m`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `m MOD 18446744073709551616 = m` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m MOD 4294967296 = m` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `m MOD 256 = m` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let PC_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let PC_SQ_SUC2 = prove(`!(S:1600 word) b. keccak_f1600 (keccak_squeeze (b + 1) S) = keccak_squeeze (b + 2) S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PC_SQ_SUC] THEN REWRITE_TAC[ARITH_RULE `(b + 1) + 1 = b + 2`]);;

let PC_ALIGN288 = SAMPLING_ALIGN32_RULE 288;;

let PC_ALIGN272 = prove
 (`!sp:int64. aligned 16 sp /\ ~aligned 32 sp
              ==> aligned 32 (word_add sp (word 272)) /\
                  aligned 16 (word_add sp (word 272))`,
  REWRITE_TAC[SAMPLING_ALIGNED_16_32] THEN GEN_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(* the sign coefficient as the code computes it, from the 32-bit view of the
   register of the signs, as a case split on the bit *)
let PC_SIGN_FIX_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes32 (word_add c (word (4 * j)))) s`) (lhs c) &&
       can (find_term (fun t -> is_comb t && (try fst(dest_const(rator(rator t))) = "word_ushr" with _ -> false))) (rhs c)
    then
      let r = rhs c in
      let ush = find_term (fun t -> is_comb t && (try fst(dest_const(rator(rator t))) = "word_ushr" with _ -> false)) r in
      let y = mk_var("y",type_of ush) in
      let r' = subst [y,ush] r in
      let lemma = prove(mk_forall(y,mk_eq(r',`if bit 0 (y:int64) then word_neg(word 1) else word 1:int32`)),
                        GEN_TAC THEN BITBLAST_TAC) in
      let lth = SPEC ush lemma in
      ASSUME_TAC(REWRITE_RULE[lth; BIT_WORD_USHR; ADD_CLAUSES; GSYM mld_poly_challenge_sign] th)
    else NO_TAC);;

let PC_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;
