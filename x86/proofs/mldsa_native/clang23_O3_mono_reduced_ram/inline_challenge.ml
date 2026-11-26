(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa{44,65,87}_poly_challenge of    *)
(* the clang 23 -O3 build (see poly_challenge_*_spec.ml). Clang inlined the  *)
(* SHAKE256 functions. Each function, after saving six registers and         *)
(* aligning its frame to 32 bytes, zeroes a Keccak state at fr + 16 (fr the  *)
(* stack pointer after the SUB of the prologue) and puts the seed and the    *)
(* padding into it with straight-line SSE code (stage A, which differs       *)
(* between the three functions and is in their proof files), then           *)
(* (stage B) calls mldsa_keccakf1600_permute, copies the first block of 136  *)
(* bytes of the state to the buffer at fr + 224 with memcpy, loads the sign  *)
(* bits from its first 8 bytes and zeroes the polynomial with memset, and    *)
(* then (stage C) reads the bytes of the buffer from position 8 on, calling  *)
(* mldsa_keccakf1600_permute and memcpy for the next block when the buffer   *)
(* is used up, swapping in a sign for each accepted byte. Stages B and C,    *)
(* the whole body (MAIN, with the zeroing of the signs, the state and the    *)
(* buffer) and the function with its prologue and epilogue have the same    *)
(* code in the three functions, apart from their offsets, the number tau of  *)
(* signs and the length of the seed, and are stated and proved here by      *)
(* generators with those as parameters. The stages with calls are stated    *)
(* from bq = fr - 296, the lowest address of the 680 bytes of the frame and  *)
(* of the stack of mldsa_keccakf1600_permute. The loop of stage C follows    *)
(* the proofs of the gcc builds (utils/mldsa_native_challenge.ml), with the  *)
(* head of the loop at the test of the position for every byte.             *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_challenge.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;


(* instantiating a template: replace each @NAME@ by its value *)
let pc_tok (kvs:(string*string) list) (s:string) =
  let rec go s (k,v) =
    let kl = String.length k in
    let b = Buffer.create (String.length s) in
    let i = ref 0 in
    while !i < String.length s do
      if !i + kl <= String.length s && String.sub s !i kl = k
      then (Buffer.add_string b v; i := !i + kl)
      else (Buffer.add_char b s.[!i]; incr i)
    done;
    Buffer.contents b in
  List.fold_left go s kvs;;

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(* bytes_N at a + j of a byte array given as a number *)
let PC_RDN n =
  let sub = pc_tok ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let wth = (match n with 8 -> BYTES8_WBYTES | 16 -> BYTES16_WBYTES | 32 -> BYTES32_WBYTES
             | 64 -> BYTES64_WBYTES | _ -> BYTES128_WBYTES) in
  prove(parse_term(sub
   "!(a:int64) m x j (s:x86state).
        read (memory :> bytes(a,m)) s = x /\\ j + @NB@ <= m
        ==> read (memory :> @BN@ (word_add a (word j))) s =
            word((x DIV 2 EXP (8 * j)) MOD 2 EXP @N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[wth; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `m:num`; `x:num`; `j:num`; parse_term(sub "@NB@"); `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC NUM_REDUCE_CONV);;
let PC_RD8 = PC_RDN 8;; let PC_RD16 = PC_RDN 16;; let PC_RD32 = PC_RDN 32;;
let PC_RD64 = PC_RDN 64;; let PC_RD128 = PC_RDN 128;;

(* pieces of a number C < 2^b as subwords of word C : b word *)
let PC_SUBW b n =
  let ty = match n with 8 -> ":byte" | 16 -> ":int16" | 32 -> ":int32" | 64 -> ":int64" | _ -> ":int128" in
  let sub = pc_tok ["@N@",string_of_int n; "@NT@",ty; "@B@",string_of_int b] in
  prove(parse_term(sub
   "!M j. M < 2 EXP @B@ /\\ 8 * j + @N@ <= @B@
         ==> word((M DIV 2 EXP (8 * j)) MOD 2 EXP @N@)@NT@ =
             word_subword (word M:@B@ word) (8 * j,@N@)"),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN (parse_term(sub "M MOD 2 EXP @B@ = M")) (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* the fact for a load of nb bytes at seed + j, as a subword of word C *)
let pc_seed_fact b j nb =
  let rd = match nb with 1 -> PC_RD8 | 2 -> PC_RD16 | 4 -> PC_RD32 | 8 -> PC_RD64 | _ -> PC_RD128 in
  let subw = PC_SUBW b (8 * nb) in
  let bt = mk_small_numeral (b / 8) in
  let th1 = MP (SPECL [`seed:int64`;bt;`C:num`;mk_small_numeral j;`s0:x86state`] rd)
    (CONJ (ASSUME (mk_eq(`read (memory :> bytes(seed,LEN)) s0`,`C:num`) |> subst[bt,`LEN:num`]))
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_small_numeral j,mk_small_numeral nb),bt))))) in
  let th2 = MP (SPECL [`C:num`; mk_small_numeral j] subw)
    (CONJ (ASSUME (mk_binary "<" (`C:num`, mk_binary "EXP" (`2`,mk_small_numeral b))))
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_binary "*" (`8`,mk_small_numeral j),mk_small_numeral (8*nb)),mk_small_numeral b))))) in
  REWRITE_RULE[WORD_ADD_0] (TRANS th1 th2);;

(* zero subfacts of a 128-bit zero fact *)
let PC_ZSUB n =
  let sub = pc_tok ["@NB@",string_of_int (n/8); "@BN@",Printf.sprintf "bytes%d" n] in
  let rd = match n with 8 -> PC_RD8 | 16 -> PC_RD16 | 32 -> PC_RD32 | _ -> PC_RD64 in
  prove(parse_term(sub
   "!(a:int64) k (s:x86state).
        read (memory :> bytes128 a) s = word 0 /\\ k + @NB@ <= 16
        ==> read (memory :> @BN@ (word_add a (word k))) s = word 0"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16`; `read (memory :> bytes(a,16)) (s:x86state)`; `k:num`; `s:x86state`] rd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(a,16)) (s:x86state) = 0` SUBST1_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes128 a) (s:x86state) = word 0` THEN
    REWRITE_TAC[MLD_READ_BYTES128] THEN
    DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_128; VAL_WORD_0] THEN
    MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  REWRITE_TAC[DIV_0; MOD_0; WORD_ADD_0]);;
let PC_ZSUB8 = PC_ZSUB 8;; let PC_ZSUB16 = PC_ZSUB 16;; let PC_ZSUB32 = PC_ZSUB 32;; let PC_ZSUB64 = PC_ZSUB 64;;

(* pc_zfact sname off k nb: from the zero fact bytes128 (fr + off) at sname, *)
(* the zero fact for the nb bytes at fr + k                                 *)
let pc_zfact sname off k nb =
  let s = mk_var(sname,`:x86state`) in
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add fr (word %d))) %s = word 0" (8*nb) k sname) in
  let lem = match nb with 1 -> PC_ZSUB8 | 2 -> PC_ZSUB16 | 4 -> PC_ZSUB32 | _ -> PC_ZSUB64 in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC(SPECL [parse_term(Printf.sprintf "word_add fr (word %d):int64" off); mk_small_numeral (k-off); s] lem) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[PTR_ADD_G] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(*** The state from its pieces ***)

let READ_MEMORY_BYTES_EXTEND = prove
 (`!d:int64 j k x s:x86state.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let PC_B16 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
let PC_B1 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;
let PC_B4 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,4)) s = val(read (memory :> bytes32 a) s)`,
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV);;
let PC_B8 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,8)) s = val(read (memory :> bytes64 a) s)`,
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let PC_PIECE_GEN n =
  let bth, nb = match n with 8 -> PC_B1,1 | 32 -> PC_B4,4 | 64 -> PC_B8,8 | _ -> PC_B16,16 in
  let ty = match n with 8 -> ":byte" | 32 -> ":int32" | 64 -> ":int64" | _ -> ":int128" in
  let sub = pc_tok ["@N@",string_of_int n; "@NT@",ty; "@NB@",string_of_int nb] in
  prove(parse_term(sub
   "!(S:1600 word) (A:int64) (s:x86state) (V@NT@) off.
     read (memory :> bytes@N@ A) s = V /\\ V = word_subword S (8 * off,@N@)
     ==> read (memory :> bytes(A,@NB@)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP @N@"),
  REPEAT STRIP_TAC THEN REWRITE_TAC[bth] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let PC_PIECE16 = PC_PIECE_GEN 128;; let PC_PIECE8 = PC_PIECE_GEN 8;;
let PC_PIECE4 = PC_PIECE_GEN 32;; let PC_PIECE64 = PC_PIECE_GEN 64;;

let PC_NORMC = TRY_CONV(REWRITE_CONV[PTR_ADD_G]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let PC_NORM = CONV_RULE PC_NORMC;;

let PC_ZX_MOD8 = prove(`!y:N word. word (val y MOD 256):byte = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* the state word: seed C of n bytes, 0x1F after it, 0x80 at byte 135 *)
let PC_SW n = parse_term(Printf.sprintf "word_or (word_zx (word C:%d word):1600 word) (word(2 EXP %d * 31 + 2 EXP 1080 * 128))" (8*n) (8*n));;

(* the piece (off,len) of the state at fr + 16 + off at the state sn *)
let PC_PIECE_THM sw asl sn off len =
  let sz,lem = match len with 16 -> "bytes128",PC_PIECE16 | 8 -> "bytes64",PC_PIECE64
                            | 4 -> "bytes32",PC_PIECE4 | _ -> "bytes8",PC_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add fr (word %d))) %s" sz (16 + off) sn) in
  let fact = try snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl)
             with Failure _ -> failwith ("PC_PIECE_THM: no fact for " ^ string_of_int off) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add fr (word %d):int64" (16 + off)) in
  let s = mk_var(sn,`:x86state`) in
  let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[PC_ZX_MOD8] THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

(* bytes(fr+16,200) = val sw at the state sn, as a chain of extensions *)
let PC_CHAIN_TAC sw pieces sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:x86state`) in
    let d = `word_add fr (word 16):int64` in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = PC_NORM(prove(
      subst [s,`s:x86state`; x,`x:num`]
       `read (memory :> bytes(word_add fr (word 16),0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = PC_NORM(PC_PIECE_THM sw asl sn off len) in
      let ext = PC_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) pieces (cur0,0) in
    ASSUME_TAC fin);;

let PC_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

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

(*** Steps of SSE code, keeping the 128-bit halves of the YMM registers ***)
let PC_SUBWORD_JOIN_LO = prove
 (`!x y:int128. word_subword (word_join x y:int256) (0,128):int128 = y`,
  CONV_TAC WORD_BLAST);;
let PC_SUBWORD_JOIN_HI = prove
 (`!x y:int128. word_subword (word_join x y:int256) (128,128):int128 = x`,
  CONV_TAC WORD_BLAST);;
let PC_SSE_STEPS_TAC execth ns =
  MAP_EVERY (fun n ->
    X86_STEPS_TAC execth [n] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PC_SUBWORD_JOIN_LO; PC_SUBWORD_JOIN_HI])) ns;;


let PC_FIRST136 = prove
 (`!(a:int64) (X:1600 word) s:x86state.
     read (memory :> wbytes a) s = X
     ==> read (memory :> bytes(a,136)) s = val X MOD 2 EXP (8 * 136)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let PC_SQ1 = prove(`!S:1600 word. keccak_f1600 S = keccak_squeeze 1 S`,
  REWRITE_TAC[keccak_squeeze; ARITH_RULE `1 = SUC 0`] THEN REWRITE_TAC[keccak_squeeze]);;
let PC_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;
let PC_SQ_SUC2 = prove(`!(S:1600 word) b. keccak_f1600 (keccak_squeeze (b + 1) S) = keccak_squeeze (b + 2) S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PC_SQ_SUC] THEN REWRITE_TAC[ARITH_RULE `(b + 1) + 1 = b + 2`]);;

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

let PC_SIGNS_VAL = prove
 (`!x. word((((x MOD 2 EXP (8 * 136)) DIV 2 EXP (8 * 0)) MOD 2 EXP 64)):int64 = word(x MOD 2 EXP 64)`,
  GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let PC_RENAME_E2 = CONV_RULE(DEPTH_CONV(fun tm ->
  if is_exists tm && name_of(fst(dest_exists tm)) = "e2"
  then ALPHA_CONV (mk_var("ec",type_of(fst(dest_exists tm)))) tm
  else failwith "PC_RENAME_E2"));;

let PC_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let PC_E2_CORE allowed =
    CONV_TAC(LAND_CONV PC_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let PC_E2_ANY allowed =
  FULL_EXISTS_E2_TAC allowed ORELSE
  (REPEAT CONJ_TAC THEN
   FIRST [PC_E2_CORE allowed; (ASM_REWRITE_TAC[] THEN NO_TAC); (CONV_TAC WORD_RULE THEN NO_TAC); (REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN NO_TAC)]);;
let PC_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [PC_E2_ANY (ref vars); LABEL_TAC name th]);;

let PC_ADDR_CONV =
  let wadd = `word_add:int64->int64->int64` and wd = `word:num->int64` in
  fun tm ->
   match tm with
     Comb(Comb(Const("word_sub",_),Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),a))),Comb(Const("word",_),b))
       when is_numeral a && is_numeral b && dest_numeral a >=/ dest_numeral b ->
         let r = mk_numeral(dest_numeral a -/ dest_numeral b) in
         prove(mk_eq(tm,mk_comb(mk_comb(wadd,x),mk_comb(wd,r))), CONV_TAC WORD_ARITH)
   | Comb(Comb(Const("word_add",_),Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),a))),Comb(Const("word",_),b)) ->
         let r = mk_comb(mk_comb(`(+):num->num->num`,a),b) in
         prove(mk_eq(tm,mk_comb(mk_comb(wadd,x),mk_comb(wd,r))), CONV_TAC WORD_RULE)
   | Comb(Comb(Const("+",_),Comb(Comb(Const("+",_),a),t)),c) when is_numeral a && is_numeral c && not(is_numeral t) ->
         let rhs = mk_comb(mk_comb(`(+):num->num->num`,mk_comb(mk_comb(`(+):num->num->num`,a),c)),t) in
         ARITH_RULE(mk_eq(tm,rhs))
   | _ -> failwith "PC_ADDR_CONV";;
let PC_ADDR_NORM = DEPTH_CONV(PC_ADDR_CONV ORELSEC NUM_ADD_CONV) THENC REWRITE_CONV[WORD_ADD_0];;
let PC_NORM_TAC = RULE_ASSUM_TAC(CONV_RULE PC_ADDR_NORM) THEN TRY(CONV_TAC PC_ADDR_NORM);;

let PC_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* the A part: from the instruction after the SUB of the prologue (a0) to   *)
(* the first call of the permutation (a1), in the frame fr of 384 bytes;    *)
(* n is the length of the seed and cl that of the constants of the function *)
let PC_A_TM fn a0 a1 n cl = parse_term(Printf.sprintf
 "exists f_events.
    forall e (c:int64) (seed:int64) (C:num) (fr:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fr /\\
      ALLPAIRS nonoverlapping [(fr,384)]
        [(seed,%d); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + %d) /\\
                read RSP s = fr /\\
                read RDI s = c /\\ read RSI s = seed /\\
                read (memory :> bytes(seed,%d)) s = C /\\
                read events s = e)
           (\\s. read RIP s = word (pc + %d) /\\
                read RSP s = fr /\\ read RBX s = c /\\
                read RDI s = word_add fr (word 16) /\\
                read R14 s = word_add fr (word 16) /\\
                read (memory :> bytes(word_add fr (word 16),200)) s =
                  val(mld_shake256_state %d C) /\\
                read (memory :> bytes32(word_add fr (word 216))) s = word 136 /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c seed C pc fr /\\
                   memaccess_inbounds e2
                    [seed,%d; fr,384%s]
                    [fr,384]))
           (MAYCHANGE [RIP; RAX; RBX; RDI; R14] ,,
            MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(fr,384)])" n (layout fn + a0) n (layout fn + a1) n n
  (if cl = 0 then "" else Printf.sprintf "; word(pc + %s_consts),%d" fn cl));;

let PC_CONST k = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc k 128;;

let PC_A_PRE execth n seedfacts =
  let b = 8 * n in
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (seed:int64) (C:num) (pc:num) (fr:int64). f_ev_a c seed C pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`)) (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3;4;5] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "C < 2 EXP %d" b)) ASSUME_TAC THENL
   [MP_TAC(ISPECL [`seed:int64`; mk_small_numeral n; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun (j,nb) -> ASSUME_TAC(pc_seed_fact b j nb)) seedfacts THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV));;

(* a zero 128-bit fact at fr + k from the zero byte facts *)
let pc_zld sname k =
  let tm = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add fr (word %d))) %s = word 0" k sname) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC(CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) THEN
    REWRITE_TAC[PTR_ADD_G] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

(* the B part: from the first call of the permutation to after memset.     *)
(* fn = function name, b0 = offset of the call, b1 = offset of after_memset *)
let PC_B_TM fn b0 b1 n = parse_term(Printf.sprintf
 "!mf mc ea el ev.
    memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (c:int64) (C:num) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        nonoverlapping (c,1024) (bq,680) /\\
        ALLPAIRS nonoverlapping [(c,1024); (bq,680)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                read RBX s = c /\\
                read RDI s = word_add bq (word 312) /\\
                read R14 s = word_add bq (word 312) /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(word_add bq (word 312),200)) s =
                  val(mld_shake256_state %d C) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                read RBX s = c /\\
                read R14 s = word_add bq (word 312) /\\
                read R15 s = word_add bq (word 520) /\\
                read R12 s = mld_poly_challenge_signs (mld_shake256_byte %d C) /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(word_add bq (word 312),200)) s =
                  val(keccak_squeeze 1 (mld_shake256_state %d C)) /\\
                read (memory :> bytes(word_add bq (word 520),136)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte %d C) 136) /\\
                (!t. t < 256
                     ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
                         word 0) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c C mf mc pc bq /\\
                   memaccess_inbounds e2
                    [c,1024; bq,680; word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [c,1024; bq,680]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [R12; R15] ,,
           MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(bq,680)])"
  (layout fn + b0) n (layout fn + b1) n n n);;

let PC_B_ALLOWED = [`c:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`; `bq:int64`];;

let PC_B_INTRO_TAC execth =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (PC_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (C:num) (mf:int64) (mc:int64) (pc:num) (bq:int64). f_ev_b c C mf mc pc bq:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `C:num`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC;;

let PC_B_BODY_TAC execth n =
  let sn = mk_small_numeral n in
  let st = subst [sn,`n:num`] `mld_shake256_state n C` in
  X86_STEPS_TAC execth [1] THEN
  KECCAK_STATE_WBYTES_TAC st THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; st; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PC_B_ALLOWED 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PC_SQ1]) THEN PC_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add bq (word 312))) s2:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PC_FIRST136 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  X86_STEPS_TAC execth (3--7) THEN PC_NORM_TAC THEN
  LIBC_PLT_TAC execth (layout "plt_memcpy") (layout "got_memcpy") 7 THEN
  PC_LIBC_CALL_TAC "H_MEMCPY" execth
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    subst [st,`S:1600 word`] `val(keccak_squeeze 1 (S:1600 word)) MOD 2 EXP (8 * 136)`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PC_B_ALLOWED 9 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  PC_NORM_TAC;;

let PC_ZERO_POLY = prove
 (`!c:int64 s:x86state.
     (!i. i < 1024 ==> read (memory :> bytes8 (word_add c (word i))) s = word_zx (word 0:int64))
     ==> !t. t < 256 ==> read (memory :> bytes32 (word_add c (word(4 * t)))) s = word 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k < 4 ==> read (memory :> bytes8 (word_add c (word(4 * t + k)))) s = word 0` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `4 * t + k`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC(LAND_CONV(DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC(CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT) THEN
  REWRITE_TAC[PTR_ADD_G; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

let PC_BUF64_TAC sn =
  let s = mk_var(sn,`:x86state`) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try lhs c = subst [s,`s:x86state`] `read (memory :> bytes(word_add bq (word 520),136)) (s:x86state)` with _ -> false)
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD_0] (MP (SPECL [`word_add (bq:int64) (word 520)`; `136`; rhs c; `0`; s] PC_RD64) (CONJ th (ARITH_RULE `0 + 8 <= 136`))))
    else NO_TAC);;

let PC_B_REST_TAC execth =
  PC_BUF64_TAC "s9" THEN
  X86_STEPS_TAC execth (10--15) THEN PC_NORM_TAC THEN
  LIBC_PLT_TAC execth (layout "plt_memset") (layout "got_memset") 15 THEN
  PC_LIBC_CALL_TAC "H_MEMSET" execth
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PC_B_ALLOWED 17 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  PC_NORM_TAC;;

let PC_MOD_MOD = CONV_RULE NUM_REDUCE_CONV (prove(`!x. ((x MOD 2 EXP 1088) DIV 1) MOD 2 EXP 64 = x MOD 2 EXP 64`, REWRITE_TAC[DIV_1; MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV));;

let PC_B_FINAL_TAC n =
  let nt = mk_small_numeral n in
  FIRST_ASSUM(fun th -> if can (term_match [] `!i. i < 1024 ==> read (memory :> bytes8 (word_add c (word i))) s = x`) (concl th)
                        then ASSUME_TAC(MATCH_MP PC_ZERO_POLY th) else NO_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[PC_SIGNS_VAL; mld_poly_challenge_signs] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [nt;`C:num`;`8`] PC_BLOCK0) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[PC_MOD_MOD];
    MP_TAC(SPECL [nt; `C:num`; `136`] PC_BLOCK0) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[th]);
    PC_SAFETY_TAC];;

let PC_B_PROVE execth fn b0 b1 n =
  prove(PC_B_TM fn b0 b1 n,
    PC_B_INTRO_TAC execth THEN PC_B_BODY_TAC execth n THEN PC_B_REST_TAC execth THEN PC_B_FINAL_TAC n);;

(* the C part: the loop over the bytes, from after_memset (c0) through the  *)
(* head hd (join2 or loop1) to the exit ex; tau coefficients, seed n bytes *)
let PC_C_TM fn c0 hd ex n tau = parse_term(Printf.sprintf
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (c:int64) (C:num) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        mld_poly_challenge_terminates %d %d C /\\
        nonoverlapping (c,1024) (bq,680) /\\
        ALLPAIRS nonoverlapping [(c,1024); (bq,680)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                read RBX s = c /\\
                read R14 s = word_add bq (word 312) /\\
                read R15 s = word_add bq (word 520) /\\
                read R12 s = mld_poly_challenge_signs (mld_shake256_byte %d C) /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes(word_add bq (word 312),200)) s =
                  val(keccak_squeeze 1 (mld_shake256_state %d C)) /\\
                read (memory :> bytes(word_add bq (word 520),136)) s =
                  num_of_bytelist(list_of_seq (mld_shake256_byte %d C) 136) /\\
                (!t. t < 256
                     ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
                         word 0) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                read RBX s = c /\\
                read R14 s = word_add bq (word 312) /\\
                read R15 s = word_add bq (word 520) /\\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add c (word(4 * i)))) s =
                         mld_poly_challenge %d %d C i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c C mc pc bq /\\
                   memaccess_inbounds e2
                    [c,1024; bq,680; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [c,1024; bq,680]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [R12; R13] ,,
           MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(bq,680)])"
  tau n (layout fn + c0) n n n (layout fn + ex) tau n);;

let pc_pc_tok l s = pc_tok l s;;

let PC_C_TEMPLATE tau n = parse_term(pc_tok ["@T@",string_of_int tau; "@N@",string_of_int n]
 "\\(c:int64) (C:num) (mc:int64) (pc:num) (bq:int64).
   APPEND
      (ENUMERATEL (mld_poly_challenge_bytes @T@ (mld_shake256_byte @N@ C))
        (\\n. if (8 + n) MOD 136 = 0
             then if mld_poly_challenge_accept @T@ (mld_shake256_byte @N@ C) n
                  then if n + 1 < mld_poly_challenge_bytes @T@ (mld_shake256_byte @N@ C)
                       then f_ev_sa c C mc pc bq n
                       else f_ev_sx c C mc pc bq n
                  else f_ev_sr c C mc pc bq n
             else if mld_poly_challenge_accept @T@ (mld_shake256_byte @N@ C) n
                  then if n + 1 < mld_poly_challenge_bytes @T@ (mld_shake256_byte @N@ C)
                       then f_ev_na c C mc pc bq n
                       else f_ev_nx c C mc pc bq n
                  else f_ev_nr c C mc pc bq n))
      (f_ev_pro c C mc pc bq:(uarch_event)list)");;

let PC_C_INV tau n = parse_term(pc_tok ["@T@",string_of_int tau; "@N@",string_of_int n; "@K@",string_of_int (256 - tau)]
 "\\n s.
    read R13 s = word(@K@ + FST(mld_poly_challenge_step @T@ (mld_shake256_byte @N@ C) n)) /\\
    read RAX s = word((7 + n) MOD 136 + 1) /\\
    read (memory :> bytes(word_add bq (word 520),136)) s =
      num_of_bytelist(list_of_seq
       (\\t. mld_shake256_byte @N@ C (136 * ((7 + n) DIV 136) + t)) 136) /\\
    read (memory :> bytes(word_add bq (word 312),200)) s =
      val(keccak_squeeze ((7 + n) DIV 136 + 1) (mld_shake256_state @N@ C)) /\\
    (!t. t < 256
         ==> read (memory :> bytes32(word_add c (word(4 * t)))) s =
             SND(mld_poly_challenge_step @T@ (mld_shake256_byte @N@ C) n) t) /\\
    read R12 s =
      word_ushr (mld_poly_challenge_signs (mld_shake256_byte @N@ C))
                (FST(mld_poly_challenge_step @T@ (mld_shake256_byte @N@ C) n)) /\\
    read RSP s = word_add bq (word 296) /\\
    read RBX s = c /\\
    read R14 s = word_add bq (word 312) /\\
    read R15 s = word_add bq (word 520) /\\
    (read DF s <=> false) /\\
    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
    read (memory :> bytes(ea,el)) s = ev");;

let PC_C_ALLOWED = [`c:int64`; `C:num`; `mc:int64`; `pc:num`; `bq:int64`; `n:num`];;

let PC_C_INTRO_TAC execth tau n =
  REPEAT GEN_TAC THEN DISCH_THEN(fun mcp ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] mcp) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (PC_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC (PC_C_TEMPLATE tau n) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `C:num`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if is_comb(concl th) && (try fst(dest_const(fst(strip_comb(concl th)))) = "mld_poly_challenge_terminates" with _ -> false)
    then ASSUME_TAC(REWRITE_RULE[mld_poly_challenge_terminates] th)
    else NO_TAC);;
let PC_C_SETUP_TAC tau n =
  let tt = mk_small_numeral tau and nt = mk_small_numeral n and kt = mk_small_numeral (256 - tau) in
  let sub = subst [tt,`TAU:num`; nt,`NN:num`; kt,`KK:num`] in
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if is_exists(concl th) then
      let nth = ASSUME (sub `n < mld_poly_challenge_bytes TAU (mld_shake256_byte NN C)`) in
      ASSUME_TAC(MP (SPEC `n:num` (CONJUNCT2
                   (MATCH_MP MLD_POLY_CHALLENGE_BYTES th))) nth) THEN
      ASSUME_TAC(MP (SPEC `n:num` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
                   MLD_POLY_CHALLENGE_BYTES_NEXT) th)) nth)
    else NO_TAC) THEN
  SUBGOAL_THEN
   (sub `mld_poly_challenge_accept TAU (mld_shake256_byte NN C) n <=>
    val(mld_shake256_byte NN C (8 + n)) <=
    KK + FST(mld_poly_challenge_step TAU (mld_shake256_byte NN C) n)`)
  ASSUME_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_accept] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC];;

let PC_C_ABBREV_TAC tau n =
  let tt = mk_small_numeral tau and nt = mk_small_numeral n and kt = mk_small_numeral (256 - tau) in
  let sub = subst [tt,`TAU:num`; nt,`NN:num`; kt,`KK:num`] in
  ABBREV_TAC (sub `k = FST (mld_poly_challenge_step TAU (mld_shake256_byte NN C) n)`) THEN
  ABBREV_TAC (sub `j = val(mld_shake256_byte NN C (8 + n))`) THEN
  SUBGOAL_THEN `j < 256` ASSUME_TAC THENL
   [EXPAND_TAC "j" THEN
    MP_TAC(ISPEC (sub `mld_shake256_byte NN C (8 + n)`) VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sub `val(word_zx(word(KK + k):int64):int32) = KK + k /\
                val(word(KK + k):int64) = KK + k /\
                val(word j:int64) = j`)
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64]] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let PC_C_NORMAL_PREP_TAC tau n =
  REWRITE_TAC[ASSUME `~((8 + n) MOD 136 = 0)`] THEN
  SUBGOAL_THEN `(7 + n) MOD 136 < 135` ASSUME_TAC THENL
   [MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_ZERO) THEN
    REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`7 + n`; `136`] MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_CHALLENGE_POS_SUC) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THEN
  MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN DISCH_TAC THEN
  ABBREV_TAC `p = (7 + n) MOD 136 + 1` THEN
  ABBREV_TAC `b = (7 + n) DIV 136` THEN
  SUBGOAL_THEN `p < 136` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word p:int64) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  PC_C_ABBREV_TAC tau n THEN
  FULL_INIT_TAC THEN
  MLD_CHALLENGE_LOAD_TAC `word_add bq (word 520):int64` `p:num`
   [ASSUME `136 * b + p = 8 + n`];;

let PC_BUF_ALIAS_TAC pt =
  let tm = subst [pt,`p:num`] `word_add (word_add bq (word 296)) (word (1 * val (word_zx (word_zx (word p:int64):int32):int64) + 224)) = word_add (bq:int64) (word (520 + p))` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC(SPEC pt MLD_CHALLENGE_ZX_ZX_WORD) THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

let PC_CMP8 = prove
 (`!x y:byte.
     (&(val x) - &(val y):int = &(val(word_sub x y)) <=> val y <= val x) /\
     (val(word_sub x y) = 0 <=> val x = val y)`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
    MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD;
                GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_SUB] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    INT_ARITH_TAC;
    REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; VAL_EQ]]);;
let PC_VAL_BYTE = prove(`!m. m < 256 ==> val(word m:byte) = m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;
let PC_IS_RIP_OR_EVENTS th =
  is_eq(concl th) &&
  (try fst(dest_const(rator(rator(lhs(concl th))))) = "read" &&
       (rand(rator(lhs(concl th))) = `RIP` || rand(rator(lhs(concl th))) = `events`)
   with _ -> false);;
let PC_JBE_TAC jt it =
  let m1 = mk_eq(mk_binop `(MOD):num->num->num` jt `256`,jt) and m2 = mk_eq(mk_binop `(MOD):num->num->num` it `256`,it) in
  let v1 = mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,jt)),jt) and v2 = mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,it)),it) in
  SUBGOAL_THEN (list_mk_conj [m1;m2;v1;v2]) (fun th ->
    let [t1;t2;t3;t4] = CONJUNCTS th in
    RULE_ASSUM_TAC(fun th' -> if PC_IS_RIP_OR_EVENTS th' then REWRITE_RULE[t3;t4] (REWRITE_RULE[PC_CMP8] (REWRITE_RULE[t1;t2] th')) else th')) THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN SIMPLE_ARITH_TAC; MATCH_MP_TAC MOD_LT THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC PC_VAL_BYTE THEN SIMPLE_ARITH_TAC; MATCH_MP_TAC PC_VAL_BYTE THEN SIMPLE_ARITH_TAC]; ALL_TAC];;

let PC_INC32 = prove
 (`!p. p + 1 < 2 EXP 32 ==> word_zx(word_add (word_zx (word p:int64):int32) (word 1)):int64 = word(p + 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `p MOD 18446744073709551616 = p /\ p MOD 4294967296 = p /\ (p + 1) MOD 4294967296 = p + 1 /\ (p + 1) MOD 18446744073709551616 = p + 1` (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let PC_RAX_INC_TAC pt =
  MP_TAC(SPEC pt PC_INC32) THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `RAX`) [ASSUME (subst [pt,`p:num`] `word_zx(word_add (word_zx (word p:int64):int32) (word 1)):int64 = word(p + 1)`)];;
let PC_C_UNABBREV_TAC tau n =
  let tt = mk_small_numeral tau and nt = mk_small_numeral n in
  let sub = subst [tt,`TAU:num`; nt,`NN:num`] in
  MLD_CHALLENGE_UNABBREV_TAC
   [sub `val(mld_shake256_byte NN C (8 + n))`,`j:num`;
    sub `FST (mld_poly_challenge_step TAU (mld_shake256_byte NN C) n)`,`k:num`;
    `(7 + n) DIV 136`,`b:num`;
    `(7 + n) MOD 136 + 1`,`p:num`];;
let PC_C_FINAL_TAC tau n =
  let it = mk_small_numeral (256 - tau) in
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MLD_POLY_CHALLENGE_STEP_ADD1] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  TRY(CONJ_TAC THENL [MLD_CHALLENGE_POLY_TAC (mk_binop `(+):num->num->num` it `k:num`); ALL_TAC]) THEN
  PC_C_UNABBREV_TAC tau n THEN
  MLD_CHALLENGE_DISCHARGE_TAC (TRY(ABBREV_TAC (subst [mk_small_numeral n,`NN:num`] `jj = val(mld_shake256_byte NN C (8 + n))`)));;

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
                        GEN_TAC THEN REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN BITBLAST_TAC) in
      let lth = SPEC ush lemma in
      ASSUME_TAC(REWRITE_RULE[lth; BIT_WORD_USHR; ADD_CLAUSES; GSYM mld_poly_challenge_sign] th)
    else NO_TAC);;

(* the byte test at steps m, m + 1 and the accepted (to step m + 12) and *)
(* rejected paths, to the end of the iteration                          *)
let PC_C_TEST_TAC execth tau n m extra =
  let tt = mk_small_numeral tau and nt = mk_small_numeral n and kt = mk_small_numeral (256 - tau) in
  let sub = subst [tt,`TAU:num`; nt,`NN:num`; kt,`KK:num`] in
  let ik = sub `KK + k` in
  let accept_tm = sub `mld_poly_challenge_accept TAU (mld_shake256_byte NN C) n` in
  let next_tm = sub `n + 1 < mld_poly_challenge_bytes TAU (mld_shake256_byte NN C)` in
  let after_stores =
    X86_STEPS_TAC execth ((m+3)--(m+12)) THEN
    MLD_CHALLENGE_EXIT_TEST_TAC THEN PC_SIGN_FIX_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_USHR_COMPOSE]) THEN
    MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `R13`) [GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
    (SUBGOAL_THEN accept_tm ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    ASM_CASES_TAC (mk_eq(`k + 1`,tt)) THENL
     [(SUBGOAL_THEN (mk_neg next_tm) ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      MLD_CHALLENGE_BRANCH_TAC THEN PC_C_FINAL_TAC tau n;
      (SUBGOAL_THEN next_tm ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      MLD_CHALLENGE_BRANCH_TAC THEN PC_C_FINAL_TAC tau n] in
  let accept =
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes32` (concl th)
      then ASSUME_TAC(MP (SPEC `j:num` th) (ASSUME `j < 256`)) else NO_TAC) THEN
    MLD_CHALLENGE_EXCLUDE_TAC ik `j:num` THEN
    X86_STEPS_TAC execth ((m+2)--(m+2)) THEN
    ASM_CASES_TAC (mk_binop `(<):num->num->bool` `j:num` ik) THEN after_stores in
  let reject =
    (SUBGOAL_THEN (mk_neg accept_tm) ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (SUBGOAL_THEN next_tm ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    PC_C_FINAL_TAC tau n in
  MLD_CHALLENGE_FIX_TAC (mld_challenge_is_read_reg `RCX`)
    [MLD_CHALLENGE_ZX_BYTE; ASSUME (sub `val(mld_shake256_byte NN C (8 + n)) = j`)] THEN
  X86_STEPS_TAC execth (m--(m+1)) THEN
  PC_JBE_TAC `j:num` ik THEN extra THEN
  ASM_CASES_TAC (mk_binop `(<=):num->num->bool` `j:num` ik) THEN MLD_CHALLENGE_BRANCH_TAC THENL
   [accept; reject];;
let PC_C_SQUEEZE_PREP_TAC tau n =
  REWRITE_TAC[ASSUME `(8 + n) MOD 136 = 0`] THEN
  SUBGOAL_THEN `(7 + n) MOD 136 = 135` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MLD_CHALLENGE_POS_ZERO] THEN
    REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_CHALLENGE_POS_WRAP) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th] THEN STRIP_ASSUME_TAC th) THEN
  MP_TAC(SPEC `7 + n` MLD_CHALLENGE_POS_SPLIT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(7 + n) + 1 = 8 + n`] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  ABBREV_TAC `b = (7 + n) DIV 136` THEN
  PC_C_ABBREV_TAC tau n THEN
  FULL_INIT_TAC;;

let PC_C_BLOCK_FACT_TAC n =
  MP_TAC(SPECL [mk_small_numeral n; `C:num`; `b + 1`; `136`] PC_BLOCK) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(b + 1) + 1 = b + 2`] THEN
  DISCH_THEN(fun th1 ->
    FIRST_X_ASSUM(fun chain ->
      if is_eq(concl chain) && rhs(concl chain) = rhs(concl th1) &&
         can (term_match [] `read (memory :> bytes(word_add bq (word 520),136)) s`) (lhs(concl chain))
      then ASSUME_TAC(REWRITE_RULE[GSYM th1] chain) else NO_TAC));;

let PC_C_NORMAL_TAC execth tau n =
  PC_C_NORMAL_PREP_TAC tau n THEN
  X86_STEPS_TAC execth (1--2) THEN
  SUBGOAL_THEN `val(word_zx(word p:int64):int32) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_CHALLENGE_VAL_ZX_WORD THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MLD_CHALLENGE_BRANCH_TAC THEN PC_BUF_ALIAS_TAC `p:num` THEN
  X86_STEPS_TAC execth (3--5) THEN
  PC_C_TEST_TAC execth tau n 6 (PC_RAX_INC_TAC `p:num`);;

let PC_C_SQUEEZE_TAC execth tau n =
  let st = subst [mk_small_numeral n,`NN:num`] `keccak_squeeze (b + 1) (mld_shake256_state NN C)` in
  let st2 = subst [mk_small_numeral n,`NN:num`] `val(keccak_squeeze (b + 2) (mld_shake256_state NN C)) MOD 2 EXP (8 * 136)` in
  PC_C_SQUEEZE_PREP_TAC tau n THEN
  X86_STEPS_TAC execth (1--4) THEN
  KECCAK_STATE_WBYTES_TAC st THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; st; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PC_C_ALLOWED 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PC_SQ_SUC2]) THEN PC_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add bq (word 312))) s5:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PC_FIRST136 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  X86_STEPS_TAC execth (6--9) THEN PC_NORM_TAC THEN
  LIBC_PLT_TAC execth (layout "plt_memcpy") (layout "got_memcpy") 9 THEN
  PC_LIBC_CALL_TAC "H_MEMCPY" execth
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; st2;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PC_C_ALLOWED 11 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  PC_NORM_TAC THEN
  X86_STEPS_TAC execth (12--14) THEN
  PC_C_BLOCK_FACT_TAC n THEN
  (SUBGOAL_THEN `136 * (b + 1) + 0 = 8 + n` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]) THEN
  MLD_CHALLENGE_LOAD_TAC `word_add bq (word 520):int64` `0` [ASSUME `136 * (b + 1) + 0 = 8 + n`] THEN
  PC_BUF_ALIAS_TAC `0` THEN
  X86_STEPS_TAC execth (15--17) THEN
  PC_C_TEST_TAC execth tau n 18 ALL_TAC;;

let PC_C_PROVE execth fn c0 hd ex n tau =
  let pcadd k = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(layout fn + k)) in
  let bytes = subst [mk_small_numeral tau,`TAU:num`; mk_small_numeral n,`NN:num`] `mld_poly_challenge_bytes TAU (mld_shake256_byte NN C)` in
  prove(PC_C_TM fn c0 hd ex n tau,
    PC_C_INTRO_TAC execth tau n THEN
    MLD_CHALLENGE_WHILE_TAC bytes (mk_abs(`n:num`,pcadd hd)) (pcadd ex) (PC_C_INV tau n) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MLD_POLY_CHALLENGE_BYTES_POS THEN ASM_REWRITE_TAC[ARITH_EQ];
      FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN
      REWRITE_TAC[CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND;
                  CONJUNCT1 mld_poly_challenge_step; WORD_USHR_ZERO] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ETA_AX] THEN
      ASM_REWRITE_TAC[ETA_AX] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
      PC_C_SETUP_TAC tau n THEN ASM_CASES_TAC `(8 + n) MOD 136 = 0` THENL
       [PC_C_SQUEEZE_TAC execth tau n; PC_C_NORMAL_TAC execth tau n];
      FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_challenge] THEN
      EXISTS_TAC `e2:(uarch_event)list` THEN ASM_REWRITE_TAC[]]);;

(* MAIN: A, B, C and the zeroing of the signs, the state and the buffer,  *)
(* from offset m0 to offset m1 (before the epilogue), in the 680 bytes at  *)
(* bq (RSP = bq + 296); cl = length of the constants of the function       *)
let PC_MAIN_TM fn m0 m1 n tau cl = parse_term(Printf.sprintf
 "!mf mc ea el ev.
    memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (c:int64) (seed:int64) (C:num) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add bq (word 296)) /\\
        mld_poly_challenge_terminates %d %d C /\\
        nonoverlapping (c,1024) (bq,680) /\\
        ALLPAIRS nonoverlapping [(c,1024); (bq,680)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)] /\\
        nonoverlapping (seed,%d) (bq,680)
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                read RDI s = c /\\ read RSI s = seed /\\
                read (memory :> bytes(seed,%d)) s = C /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read events s = e)
          (\\s. read RIP s = word (pc + %d) /\\
                read RSP s = word_add bq (word 296) /\\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add c (word(4 * i)))) s =
                         mld_poly_challenge %d %d C i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events c seed C mf mc pc bq /\\
                   memaccess_inbounds e2
                    [seed,%d; c,1024; bq,680; word(pc + got_memset),8;
                     word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192%s]
                    [c,1024; bq,680]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [RBX; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(c,1024); memory :> bytes(bq,680)])"
  tau n n (layout fn + m0) n (layout fn + m1) tau n n
  (if cl = 0 then "" else Printf.sprintf "; word(pc + %s_consts),%d" fn cl));;

let PC_MAIN_ALLOWED = [`c:int64`; `seed:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`; `bq:int64`];;
let PC_MCALL execth name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PC_E2_ANY (ref PC_MAIN_ALLOWED); LABEL_TAC name th]);;

let PC_MAIN_PROVE execth fn m0 m1 n tau cl tha thb thc =
  prove(PC_MAIN_TM fn m0 m1 n tau cl,
  (REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`mc:int64`;`ea:int64`;`el:num`;`ev:num`] thb) th) "H_B" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] thc) mcp) "H_C") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC tha "H_A" THEN
  CONCRETIZE_F_EVENTS_TAC `\(c:int64) (seed:int64) (C:num) (mf:int64) (mc:int64) (pc:num) (bq:int64). f_ev_main c seed C mf mc pc bq:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c:int64`; `seed:int64`; `C:num`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
  FULL_INIT_TAC THEN
  PC_MCALL execth "H_A" [`c:int64`; `seed:int64`; `C:num`; `read RSP s`; `pc:num`] 1 THEN
  PC_NORM_TAC THEN
  PC_MCALL execth "H_B" [`c:int64`; `C:num`; `bq:int64`; `pc:num`] 2 THEN PC_NORM_TAC THEN
  PC_MCALL execth "H_C" [`c:int64`; `C:num`; `bq:int64`; `pc:num`] 3 THEN PC_NORM_TAC THEN
  PC_SSE_STEPS_TAC execth (4--31) THEN PC_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN PC_SAFETY_TAC);;

let PC_TOP_ALLOWED = [`c:int64`; `seed:int64`; `C:num`; `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`; `bot:int64`];;
let PC_TOP_MCALL execth name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,execth,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PC_E2_ANY (ref PC_TOP_ALLOWED); LABEL_TAC name th]);;

let PC_TOP_TAC execth n mainth =
  let nt = mk_small_numeral n in
  (REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`mc:int64`;`ea:int64`;`el:num`;`ev:num`] mainth) th) "H_MAIN") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(c:int64) (seed:int64) (C:num) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
     f_ev_all c seed C mf mc pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  (REALIGN_TAC 711 THEN REALIGN_FRAME_TAC 759 711 THEN
  REALIGN_NONOV_TAC 680
   [`c:int64,1024`; subst [nt,`n:num`] `seed:int64,n:num`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 711):int64,48`;
    `word_add stackpointer (word 759):int64,8`] THEN
  REALIGN_ALIGNED_TAC [296]) THEN
  (ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15`) THEN
  (FULL_INIT_TAC THEN X86_STEPS_TAC execth (1--8) THEN REALIGN_RSP_TAC THEN X86_STEPS_TAC execth (9--9)) THEN
  (PC_TOP_MCALL execth "H_MAIN" [`c:int64`; `seed:int64`; `C:num`; `bot:int64`; `pc:num`] 10) THEN
  (X86_STEPS_TAC execth (11--23)) THEN
  (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
