(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proof of mldsa_poly_uniform of the clang 23 -O3 build, on  *)
(* the regions of its code between the calls: the zeroing of the Keccak      *)
(* state and the absorbing of the seed (PU_A), the loop of five squeezes of  *)
(* the first blocks with mldsa_keccakf1600_permute and memcpy (PU_B), and    *)
(* the two loops of rejection sampling that clang made of mld_rej_uniform_c: *)
(* PU_SCAN1 over the 840 bytes of the first five blocks and PU_SCAN2 over a  *)
(* block of 168 bytes, from the count so far. The frame is at fixed offsets  *)
(* from the stack pointer after the SUB of the prologue (state at +16, its   *)
(* position at +216, buffer at +224); where the stacks of callees are used,  *)
(* the lemma is stated from bq, the lowest address of the 1384 bytes of the  *)
(* frame, the stack pointer being bq + 296.                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;


(* ----- a_stmt.ml ----- *)
let PU_EXEC = MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

let PU_A_TM = parse_term
 "exists f_events.
    forall e (a:int64) (seed:int64) (M:num) (fr:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fr /\\
      ALLPAIRS nonoverlapping [(fr,1088)]
        [(seed,34); (word pc,libmldsa_size)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + 144008) /\\
                read RSP s = fr /\\
                read RDI s = a /\\ read RSI s = seed /\\
                read (memory :> bytes(seed,34)) s = M /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa_poly_uniform_join3) /\\
                read RSP s = fr /\\ read RBX s = a /\\ read RSI s = seed /\\
                read R12 s = word 168 /\\ read R13 s = word 840 /\\
                read R14 s = word 0 /\\
                read (memory :> bytes(word_add fr (word 16),200)) s =
                  val(mld_keccak_absorb_once 168 0x1F 34 M) /\\
                read (memory :> bytes32(word_add fr (word 216))) s = word 168 /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a seed M pc fr /\\
                   memaccess_inbounds e2
                    [seed,34; fr,1088] [fr,1088]))
           (MAYCHANGE [RIP; RAX; RBX; RDX; R12; R13; R14] ,,
            MAYCHANGE [ZMM0; ZMM1] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(fr,1088)])";;

(* ----- pu_lib.ml ----- *)
let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;
(*** The absorbed state of a seed of 34 bytes as a number ***)

let PU_ABSORB_VAL = prove
 (`!M. M < 2 EXP 272
       ==> val(mld_keccak_absorb_once 168 0x1F 34 M:1600 word) =
           M + 2 EXP 272 * 31 + 2 EXP 1336 * 128`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MLD_KECCAK_ABSORB_ONCE] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SIMP_TAC[MLD_KECCAK_PAD_SHORT; ARITH_RULE `34 + 2 <= 168`; ARITH_RULE `31 < 256`] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  SUBGOAL_THEN `(M + 2 EXP (8 * 34) * (31 + 2 EXP (8 * (168 - 34 - 1)) * 128)) = M + 2 EXP 272 * 31 + 2 EXP 1336 * 128` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD; ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `(M + 2 EXP 272 * 31 + 2 EXP 1336 * 128) < 2 EXP 1344` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP 272` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * 168 = 1344`] THEN ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM(fun th -> MP_TAC th) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The absorbed state as a 1600-bit word: the seed, the padding byte 0x1F
     after it and the padding byte 0x80 at the end of the rate ***)

let PU_S_WORD = prove
 (`!M. M < 2 EXP (8 * 34)
       ==> mld_keccak_absorb_once 168 0x1F 34 M =
           word_or (word_zx (word M:272 word):1600 word)
                   (word(2 EXP 272 * 31 + 2 EXP 1336 * 128))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `M < 2 EXP 272` ASSUME_TAC THENL
   [UNDISCH_TAC `M < 2 EXP (8 * 34)` THEN REWRITE_TAC[ARITH_RULE `8 * 34 = 272`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PU_ABSORB_VAL; ARITH_RULE `8 * 34 = 272`] THEN
  SUBGOAL_THEN `(word_zx (word M:272 word):1600 word) || word (2 EXP 272 * 31 + 2 EXP 1336 * 128) = word_add (word_zx (word M:272 word):1600 word) (word (2 EXP 272 * 31 + 2 EXP 1336 * 128))` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP 272 * 31 + 2 EXP 1336 * 128 < 2 EXP 1600` ASSUME_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `M < 2 EXP 1600` ASSUME_TAC THENL [UNDISCH_TAC `M < 2 EXP 272` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `M + 2 EXP 272 * 31 + 2 EXP 1336 * 128 < 2 EXP 1600` ASSUME_TAC THENL [UNDISCH_TAC `M < 2 EXP 272` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_CONV `dimindex(:272)`] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `MIN 272 1600 = 272`] THEN
  SUBGOAL_THEN `M MOD 2 EXP 272 = M` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `M + a + b = M + (a + b)`]);;

(*** Facts about the bytes of the seed, and splitting of zero stores ***)

let PU_BYTE_SUB = prove
 (`!M j. M < 2 EXP (8 * 34)
         ==> word((M DIV 2 EXP (8 * j)) MOD 256):byte =
             word_subword (word M:272 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `M < 2 EXP 272` ASSUME_TAC THENL [UNDISCH_TAC `M < 2 EXP (8 * 34)` THEN REWRITE_TAC[ARITH_RULE `8 * 34 = 272`]; ALL_TAC] THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `M MOD 2 EXP 272 = M` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; LE_REFL; MOD_MOD_REFL; ARITH_RULE `2 EXP 8 = 256`]);;
(* the bytes of the seed as subwords of word M *)
let SEED_HYP = `!j. j < 34 ==> read (memory :> bytes8 (word_add seed (word j))) s0 = word_subword (word M:272 word) (8 * j,8)`;;
let PU_SEED_FACT sz k =
  let hth = ASSUME SEED_HYP in
  let insts = map (fun i ->
    let j = k + i in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`34`)))) in
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
  DISCH SEED_HYP th2;;
let PU_SEED_BYTE j = ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV) (MP (SPEC (mk_small_numeral j) (ASSUME SEED_HYP)) (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`34`))))));;

let PU_UNSPLIT = CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT @ [PTR_ADD_G; GSYM ADD_ASSOC; WORD_ADD_0];;
let PU_ZSPLIT sname off =
  let s = mk_var(sname,`:x86state`) in
  let tm = subst [s,`s0:x86state`; mk_small_numeral off,`OFF:num`]
    `read (memory :> bytes128 (word_add fr (word OFF))) s0 = word 0:int128` in
  FIRST_ASSUM(fun th ->
    if concl th = tm then
      let th1 = REWRITE_RULE PU_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let ths = map (CONV_RULE(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC ths
    else NO_TAC);;
let PU_ZLD_TAC sname sz k =
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add fr (word %d))) %s = word 0" (8*sz) k sname) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC(butlast PU_UNSPLIT |> fun _ -> [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC]) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

(*** The state after the absorbing, from its pieces ***)

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

let PU_B16 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
let PU_B1 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;

let PU_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_B16] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let PU_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_B1] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let PU_SW = `word_or (word_zx (word M:272 word):1600 word) (word(2 EXP 272 * 31 + 2 EXP 1336 * 128))`;;
let PU_NORMC = TRY_CONV(REWRITE_CONV[PTR_ADD_G]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let PU_NORM = CONV_RULE PU_NORMC;;

let PU_ZX_MOD8 = prove(`!y:N word. word (val y MOD 256):byte = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* the piece of length len at offset off from fr + 16 at the state sn *)
let PU_PIECE_THM asl sn off len =
  let sz,lem = if len = 16 then "bytes128",PU_PIECE16 else "bytes8",PU_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add fr (word %d))) %s" sz (16 + off) sn) in
  let fact = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add fr (word %d):int64" (16 + off)) in
  let s = mk_var(sn,`:x86state`) in
  let inst = SPECL [PU_SW; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[PU_ZX_MOD8] THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

let PU_PIECES =
  [0,16; 16,1; 17,16; 33,1; 34,1] @ map (fun j -> j,1) (35--39) @
  map (fun j -> j,16) [40;56;72;88;104;120;136] @ map (fun j -> j,1) (152--167) @
  [168,16; 184,16];;

(* bytes(fr+16,200) = val Sw at the state sn, as a chain of extensions *)
let PU_CHAIN_TAC sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:x86state`) in
    let d = `word_add fr (word 16):int64` in
    let x = mk_comb(`val:1600 word->num`,PU_SW) in
    let cur0 = PU_NORM(prove(
      subst [s,`s:x86state`; x,`x:num`]
       `read (memory :> bytes(word_add fr (word 16),0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = PU_NORM(PU_PIECE_THM asl sn off len) in
      let ext = PU_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) PU_PIECES (cur0,0) in
    ASSUME_TAC fin);;


(* ------------------------------------------------------------------------- *)
(* From the stack check to the loop that squeezes the five blocks (65        *)
(* instructions): zero the context, absorb the seed and the padding.         *)
(* ------------------------------------------------------------------------- *)


(* ----- rdn.ml ----- *)
let PU_RDN n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
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
let PU_RD8 = PU_RDN 8;; let PU_RD64 = PU_RDN 64;; let PU_RD128 = PU_RDN 128;; let PU_RD32 = PU_RDN 32;;

(* ----- subw.ml ----- *)
let PU_SUBW n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NT@",(match n with 8 -> ":byte" | 64 -> ":int64" | _ -> ":int128");
                          "@DI@",(match n with 8 -> "DIMINDEX_8" | 64 -> "DIMINDEX_64" | _ -> "DIMINDEX_128")] in
  prove(parse_term(sub
   "!M j. M < 2 EXP 272 /\\ 8 * j + @N@ <= 272
         ==> word((M DIV 2 EXP (8 * j)) MOD 2 EXP @N@)@NT@ =
             word_subword (word M:272 word) (8 * j,@N@)"),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `M MOD 2 EXP 272 = M` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;
let PU_SUBW8 = PU_SUBW 8;; let PU_SUBW64 = PU_SUBW 64;; let PU_SUBW128 = PU_SUBW 128;;

(* ----- zsub.ml ----- *)
let PU_ZSUB n =
  let sub = subst_tokens ["@NB@",string_of_int (n/8); "@BN@",Printf.sprintf "bytes%d" n] in
  prove(parse_term(sub
   "!(a:int64) k (s:x86state).
        read (memory :> bytes128 a) s = word 0 /\\ k + @NB@ <= 16
        ==> read (memory :> @BN@ (word_add a (word k))) s = word 0"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16`; `read (memory :> bytes(a,16)) (s:x86state)`; `k:num`; `s:x86state`]
    (match n with 8 -> PU_RD8 | 64 -> PU_RD64 | _ -> failwith "zsub")) THEN
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
let PU_ZSUB8 = PU_ZSUB 8;; let PU_ZSUB64 = PU_ZSUB 64;;
let pu_zfact sname off k nb =
  let s = mk_var(sname,`:x86state`) in
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add fr (word %d))) %s = word 0" (8*nb) k sname) in
  let lem = if nb = 1 then PU_ZSUB8 else PU_ZSUB64 in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC(SPECL [parse_term(Printf.sprintf "word_add fr (word %d):int64" off); mk_small_numeral (k-off); s] lem) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[PTR_ADD_G] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(* ----- a_proof.ml ----- *)
let PU_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

let pu_seed_fact rd subw j nb =
  let th1 = MP (SPECL [`seed:int64`;`34`;`M:num`;mk_small_numeral j;`s0:x86state`] rd)
    (CONJ (ASSUME `read (memory :> bytes(seed,34)) s0 = M`)
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_small_numeral j,mk_small_numeral nb),`34`))))) in
  let th2 = MP (SPECL [`M:num`; mk_small_numeral j] subw)
    (CONJ (ASSUME `M < 2 EXP 272`)
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_binary "*" (`8`,mk_small_numeral j),mk_small_numeral (8*nb)),`272`))))) in
  REWRITE_RULE[WORD_ADD_0] (TRANS th1 th2);;

let PU_A_TAC =
  CONCRETIZE_F_EVENTS_TAC `\(a:int64) (seed:int64) (M:num) (pc:num) (fr:int64). f_ev_a1 a seed M pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`)) (parse_term(Printf.sprintf "read YMM%d" n))) [0;1] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `M < 2 EXP 272` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`seed:int64`; `34`; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY (fun (rd,sw,j,nb) -> ASSUME_TAC(pu_seed_fact rd sw j nb))
    [PU_RD128,PU_SUBW128,0,16; PU_RD8,PU_SUBW8,16,1; PU_RD64,PU_SUBW64,17,8;
     PU_RD64,PU_SUBW64,25,8; PU_RD8,PU_SUBW8,33,1] THEN
  VERIF_SSE_STEPS_TAC PU_EXEC (1--17) THEN
  pu_zfact "s17" 40 41 8 THEN
  VERIF_SSE_STEPS_TAC PU_EXEC (18--22) THEN
  MAP_EVERY (fun k -> pu_zfact "s22" 40 k 1) (49--55) THEN
  VERIF_SSE_STEPS_TAC PU_EXEC (23--27) THEN
  MAP_EVERY (fun k -> pu_zfact "s27" 168 k 1) (168--183) THEN
  VERIF_SSE_STEPS_TAC PU_EXEC (28--33) THEN
  PU_CHAIN_TAC "s33" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `M:num` PU_S_WORD) THEN
    ANTS_TAC THENL [REWRITE_TAC[ARITH_RULE `8 * 34 = 272`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PU_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_A = prove(PU_A_TM, PU_A_TAC);;

(* ----- c_lib.ml ----- *)
let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;
let PU_VAL_ADD = prove(`!x k. x + k < 2 EXP 64 ==> val(word_add (word x:int64) (word k)) = x + k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `x < 2 EXP 64 /\ k < 2 EXP 64` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]);;
let PU_VAL_WORD = prove(`!c. c < 2 EXP 64 ==> val(word c:int64) = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]);;
let PU_ZX64_32 = prove(`!t. t < 2 EXP 32 ==> word_zx(word t:int64):int32 = word t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `t < 2 EXP 64` (fun th -> ASM_SIMP_TAC[th; MOD_LT; MOD_LT_EQ]) THEN ASM_ARITH_TAC);;
let PU_BYTE_FACT k =
  let t = subst [k,`k:num`] `read (memory :> bytes8 (word_add fr (word (224 + 3 * i + k)))) s0 = (b:num->byte) (3 * i + k)` in
  let eqt = subst [k,`k:num`] `word_add (word_add fr (word 224)) (word (3 * i + k)):int64 = word_add fr (word (224 + 3 * i + k))` in
  SUBGOAL_THEN t (ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES]) THENL
   [SUBGOAL_THEN eqt ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th) then MP_TAC(SPEC (subst [k,`k:num`] `3 * i + k`) th) else NO_TAC) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; REWRITE_TAC[ASSUME eqt] THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC];;
let PU_CAND_RAW = prove(`!(b:num->byte) i. word_insert (word_zx (word_join (b (3 * i + 1)) (b (3 * i)):int16):int32) (16,7) (word_zx (b (3 * i + 2)):int32) = mld_rej_uniform_cand b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_cand] THEN BITBLAST_TAC);;

let PU_G_FACTS = prove(`!(b:num->byte) G. mld_rej_uniform_groups 256 0 b 840 = G
  ==> LENGTH(mld_rej_uniform_list b G) <= 256 /\
      MIN 256 (LENGTH(mld_rej_uniform_list b 280)) = LENGTH(mld_rej_uniform_list b G) /\
      (!k. k < LENGTH(mld_rej_uniform_list b G)
           ==> EL k (mld_rej_uniform_list b 280) = EL k (mld_rej_uniform_list b G))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_GROUPS) THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (b:num->byte) G) <= 256` ASSUME_TAC THENL
   [ASM_CASES_TAC `G = 0` THENL
     [ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; ARITH_RULE `0 <= n`];
      SUBGOAL_THEN `?g. G = g + 1` STRIP_ASSUME_TAC THENL [EXISTS_TAC `G - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:num` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[ARITH_RULE `g < g + 1`] THEN
      REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
      COND_CASES_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`256`; `0`; `b:num->byte`; `840`] MLD_REJ_UNIFORM_CTR) THEN
    MP_TAC(SPEC `b:num->byte` MLD_REJ_UNIFORM_CTR_FIRST) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EL_MLD_REJ_UNIFORM_LIST_PREFIX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `G <= 840 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The first loop.                                                           *)
(* ------------------------------------------------------------------------- *)

(* ----- b_stmt.ml ----- *)
let PU_B_TM = parse_term
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (a:int64) (S:1600 word) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALLPAIRS nonoverlapping [(bq,1384)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + mldsa_poly_uniform_join3) /\\
                read RSP s = word_add bq (word 296) /\\ read RBX s = a /\\
                read R12 s = word 168 /\\ read R13 s = word 840 /\\
                read R14 s = word 0 /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add bq (word 312),200)) s = val(S:1600 word) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + 144295) /\\
                read RSP s = word_add bq (word 296) /\\ read RBX s = a /\\
                read R12 s = word 168 /\\ read R13 s = word 0 /\\
                read R14 s = word 840 /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add bq (word 312),200)) s =
                  val(keccak_squeeze 5 S) /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add bq (word 520)) (word j))) s =
                         mld_keccak_squeeze_byte 168 S 168 j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events bq mc pc /\\
                   memaccess_inbounds e2
                    [bq,1384; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [bq,1384]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(bq,1384)])";;

(* ----- b_lem.ml ----- *)
let PU_FIRST168 = prove
 (`!(a:int64) (X:1600 word) s:x86state.
     read (memory :> wbytes a) s = X
     ==> read (memory :> bytes(a,168)) s = val X MOD 2 EXP (8 * 168)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let PU_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let PU_NSUM_SUC = prove(`!(f:num->num) i. nsum {j | j < i + 1} f = nsum {j | j < i} f + f i`, REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT]);;

let PU_EXTBLK = prove
 (`!(bq:int64) i (S:1600 word) s:x86state.
     read (memory :> bytes(word_add bq (word 520),168 * i)) s =
       nsum {j | j < i} (\j. 2 EXP (8 * 168 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168)) /\
     read (memory :> bytes(word_add bq (word (520 + 168 * i)),168)) s =
       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)
     ==> read (memory :> bytes(word_add bq (word 520),168 * (i + 1))) s =
       nsum {j | j < i + 1} (\j. 2 EXP (8 * 168 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_NSUM_SUC; READ_COMPONENT_COMPOSE; ARITH_RULE `168 * (i + 1) = 168 * i + 168`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  SUBGOAL_THEN `word_add (word_add bq (word 520)) (word (168 * i)):int64 = word_add bq (word (520 + 168 * i))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[ARITH_RULE `8 * 168 * i = 8 * (168 * i)`]);;

let PU_B_INV =
 `\i s. read RSP s = word_add bq (word 296) /\ read RBX s = a /\ read R12 s = word 168 /\
        read R13 s = word (840 - 168 * i) /\ read R14 s = word (168 * i) /\
        (read DF s <=> false) /\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        read (memory :> bytes (word_add bq (word 312),200)) s = val(keccak_squeeze i S) /\
        read (memory :> bytes(word_add bq (word 520),168 * i)) s =
          nsum {j | j < i} (\j. 2 EXP (8 * 168 * j) *
                                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168))`;;

let PU_B_ALLOWED = [`bq:int64`; `mc:int64`; `pc:num`; `i:num`; `a:int64`; `S:1600 word`];;
let PU_RENAME_E2 = CONV_RULE(DEPTH_CONV(fun tm ->
  if is_exists tm && name_of(fst(dest_exists tm)) = "e2"
  then ALPHA_CONV (mk_var("ec",type_of(fst(dest_exists tm)))) tm
  else failwith "PU_RENAME_E2"));;

let PU_B_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (PU_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC `\(bq:int64) (mc:int64) (pc:num). APPEND (f_ev_epil bq mc pc) (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c bq mc pc i else f_ev_l bq mc pc i)) (f_ev_prol bq mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `S:1600 word`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC);;

(* ----- b_proof.ml ----- *)
let PU_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let PU_E2_CORE allowed =
    CONV_TAC(LAND_CONV PU_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let PU_E2_TAC allowed =
  (CONJ_TAC THENL [CONV_TAC WORD_RULE; PU_E2_CORE allowed]) ORELSE PU_E2_CORE allowed;;
let PU_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [(FULL_EXISTS_E2_TAC (ref vars) ORELSE PU_E2_TAC (ref vars)); LABEL_TAC name th]);;
let PU_VAL168 = prove(`!i. i < 5 ==> val(word(168 * i):int64) = 168 * i`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
  UNDISCH_TAC `i < 5` THEN ARITH_TAC);;
let PU_ADDR_CONV =
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
   | _ -> failwith "PU_ADDR_CONV";;
let PU_ADDR_NORM = DEPTH_CONV(PU_ADDR_CONV ORELSEC NUM_ADD_CONV) THENC REWRITE_CONV[WORD_ADD_0];;
let PU_NORM_TAC = RULE_ASSUM_TAC(CONV_RULE PU_ADDR_NORM) THEN TRY(CONV_TAC PU_ADDR_NORM);;
let PU_ARITH = prove(`!i. i < 5 ==> word_sub (word (840 - 168 * i)) (word 168):int64 = word (840 - 168 * (i + 1)) /\ (val(word_sub (word (840 - 168 * i)) (word 168):int64) = 0 <=> ~(i + 1 < 5)) /\ word_add (word (168 * i)) (word 168):int64 = word (168 * (i + 1))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let PU_CSEL = prove(`!i. i < 5 ==> (if val(word(840 - 168 * i):int64) < 168 then word(840 - 168 * i):int64 else word 168) = word 168`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let PU_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let PU_BODY_FINAL_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [MP_TAC(SPECL [`bq:int64`; `i:num`; `S:1600 word`; `s21:x86state`] PU_EXTBLK) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
         REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN PU_SAFETY_TAC];;

let PU_B_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC PU_EXEC (1--4) THEN PU_NORM_TAC THEN
  KECCAK_STATE_WBYTES_TAC `keccak_squeeze i S` THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PU_EXEC "H_PERM"
   [`read RDI s`; `keccak_squeeze i S`; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PU_B_ALLOWED 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_SQ_SUC]) THEN PU_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add bq (word 312))) s5:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PU_FIRST168 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  X86_STEPS_TAC PU_EXEC (6--15) THEN PU_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` PU_CSEL) (ASSUME `i < 5`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` PU_VAL168) (ASSUME `i < 5`); MULT_CLAUSES]) THEN PU_NORM_TAC THEN
  LIBC_PLT_TAC PU_EXEC (layout "plt_memcpy") (layout "got_memcpy") 15 THEN
  PU_LIBC_CALL_TAC "H_MEMCPY" PU_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PU_B_ALLOWED 17 THEN
  X86_STEPS_TAC PU_EXEC (18--21) THEN PU_NORM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` PU_ARITH) (ASSUME `i < 5`)]) THEN
  REWRITE_TAC[MP (SPEC `i:num` PU_ARITH) (ASSUME `i < 5`)] THEN PU_NORM_TAC THEN
  ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[] THEN PU_BODY_FINAL_TAC;;

let PU_B_EXIT_TAC =
  FULL_INIT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `168 * 5 = 840`]) THEN
  CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[ARITH_RULE `168 * 5 = 840`] (SPECL [`word_add bq (word 520):int64`; `168`; `5`; `S:1600 word`; `s0:x86state`] MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 168`]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_B_INIT_TAC =
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
  REPEAT CONJ_TAC THEN REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  TRY DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_B = prove(PU_B_TM,
  PU_B_INTRO_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` `pc + mldsa_poly_uniform_join3` `pc + 144295` PU_B_INV THEN
  REPEAT CONJ_TAC THENL [ARITH_TAC; PU_B_INIT_TAC; PU_B_BODY_TAC; PU_B_EXIT_TAC]);;

(* ----- c_scan1_defs.ml ----- *)
let PU_SCAN1_TM = parse_term
 "exists f_events.
    forall e (a:int64) (fr:int64) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      nonoverlapping (a,1024) (word_add fr (word 224),840) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(a,1024); (word_add fr (word 224),840)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + mldsa_poly_uniform_loop1) /\\
                read RSP s = fr /\\ read RBX s = a /\\
                read RAX s = word 3 /\\ read RSI s = word 0 /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa_poly_uniform_loop1_exit) /\\
                read RSP s = fr /\\ read RBX s = a /\\
                read RSI s = word (MIN 256 (LENGTH(mld_rej_uniform_list b 280))) /\\
                (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list b 280))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list b 280)) /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a fr b pc /\\
                   memaccess_inbounds e2
                    [a,1024; word_add fr (word 224),840]
                    [a,1024]))
           (MAYCHANGE [RIP; RAX; RCX; RDX; RSI] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024)])";;

let PU_S1_TEMPLATE =
 `\(a:int64) (fr:int64) (b:num->byte) (pc:num).
    APPEND (f_ev_epil a fr b pc)
     (APPEND
       (ENUMERATEL (mld_rej_uniform_groups 256 0 b 840)
         (\i. if i + 1 < mld_rej_uniform_groups 256 0 b 840
              then if val(mld_rej_uniform_cand b i) < 8380417
                   then f_ev_a a fr b pc i else f_ev_r a fr b pc i
              else if mld_rej_uniform_groups 256 0 b 840 = 280
                   then if val(mld_rej_uniform_cand b i) < 8380417
                        then f_ev_ah a fr b pc i else f_ev_rh a fr b pc i
                   else f_ev_af a fr b pc i))
       (f_ev_prol a fr b pc)):(uarch_event)list`;;

let PU_S1_INV =
 `\i s. read RSP s = fr /\ read RBX s = a /\
        (if i < mld_rej_uniform_groups 256 0 (b:num->byte) 840
         then read RAX s = word (3 * (i + 1)) /\
              read RSI s = word (LENGTH(mld_rej_uniform_list b i))
         else read RSI s = word (LENGTH(mld_rej_uniform_list b i))) /\
        (!j. j < 840
             ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\
        (!k. k < LENGTH(mld_rej_uniform_list b i)
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 EL k (mld_rej_uniform_list b i))`;;
let PU_S1_INV_G =
 `\i s. read RSP s = fr /\ read RBX s = a /\
        (i < G ==> read RAX s = word (3 * (i + 1))) /\
        read RSI s = word (LENGTH(mld_rej_uniform_list b i)) /\
        (!j. j < 840
             ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\
        (!k. k < LENGTH(mld_rej_uniform_list b i)
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 EL k (mld_rej_uniform_list b i))`;;
let PU_DECIDE_FLAGS64_TAC =
  let pat64 = `word_sub (word x) (word y):int64` in
  W(fun (asl,w) ->
    let tml = list_mk_conj(map (concl o snd) asl) in
    let jobs = map (fun t -> t,WORD_CMP_64_FLAGS)
                   (setify (find_terms (can (term_match [] pat64)) tml)) in
    MAP_EVERY (fun (t,cth) ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] cth) THEN
          ANTS_TAC THENL
           [CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) jobs) THEN
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(SAMPLING_DECIDE_PROP_TAC p)) ps);;

let PU_STEP_TAC execth n (asl,w) =
  (SAMPLING_STEP_TAC execth n THEN
   TRY PU_DECIDE_FLAGS64_TAC THEN TRY SAMPLING_DECIDE_CONDS_TAC THEN TRY SAMPLING_DECIDE_BRANCH_TAC) (asl,w);;
let rec PU_RUN_TAC execth n stop (asl,w) =
  (PU_STEP_TAC execth n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `RIP` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else PU_RUN_TAC execth (n + 1) stop g)) (asl,w);;

(* ----- c_scan1_proof_pre.ml ----- *)
let PU_C_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < G`) o check (fun th -> is_forall(concl th) && can (term_match [] `!m. m < G ==> P m`) (concl th))) THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN (let th = ASSUME `i < G` in RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MAP_EVERY PU_BYTE_FACT [`0`;`1`;`2`] THEN
  SUBGOAL_THEN `read (memory :> bytes16 (word_add fr (word (224 + 3 * i)))) s0 = word_join ((b:num->byte) (3 * i + 1)) (b (3 * i))` ASSUME_TAC THENL
   [REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    SUBGOAL_THEN `word_add (word_add fr (word (224 + 3 * i))) (word 1):int64 = word_add fr (word (224 + 3 * i + 1))` ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (3 * (i + 1)):int64) = 3 * (i + 1)` ASSUME_TAC THENL [MATCH_MP_TAC PU_VAL_WORD THEN UNDISCH_TAC `i < 840 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (fr:int64) (word (1 * 3 * (i + 1) + 221)) = word_add fr (word (224 + 3 * i))` ASSUME_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (fr:int64) (word (1 * 3 * (i + 1) + 223)) = word_add fr (word (224 + 3 * i + 2))` ASSUME_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_UNIFORM_GROUPS_NEXT (CONJ (ASSUME `mld_rej_uniform_groups 256 0 (b:num->byte) 840 = G`) (ASSUME `i < G`))) THEN
  MP_TAC(ISPECL [`word_or (word_or (word_zx((b:num->byte)(3 * i))) (word_shl (word_zx(b(3 * i + 1))) 8)) (word_shl (word_zx(b(3 * i + 2))) 16):int32`; `8388607`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  REWRITE_TAC[GSYM mld_rej_uniform_cand] THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
  ABBREV_TAC `c = LENGTH(mld_rej_uniform_list (b:num->byte) i)` THEN
  ABBREV_TAC `tv = val(mld_rej_uniform_cand (b:num->byte) i)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mld_rej_uniform_cand (b:num->byte) i = word tv` ASSUME_TAC THENL [EXPAND_TAC "tv" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  X86_STEPS_TAC PU_EXEC (1--5) THEN
  SAMPLING_REG_TAC `RCX` `word_zx(mld_rej_uniform_cand (b:num->byte) i):int64` [mld_rej_uniform_cand] THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && can (term_match [] `read c s`) (lhs(concl th)) then REWRITE_RULE [ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th else th);;


let PU_IFF_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `i + 1 < G` then MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC;;
let PU_C_STORE_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_CASES_TAC `k < c` THENL
   [REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(k:num) = c` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`; ARITH_RULE `~(c < c)`; SUB_REFL; EL; HD] THEN
    ASM_REWRITE_TAC[]];;

let PU_C_STORE_REJ_TAC =
  REWRITE_TAC[ADD_CLAUSES; APPEND_NIL] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) then MATCH_MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[];;

let PU_C_HEAD = `word(pc+144320):int64` and PU_C_EXIT = `word(pc+144379):int64`;;

let PU_C_PATH_GEN fin =
  PU_RUN_TAC PU_EXEC 6 [PU_C_HEAD; PU_C_EXIT] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[WORD_VAL] THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ADD_CLAUSES] THEN NO_TAC) THEN
  TRY(PU_C_STORE_TAC THEN NO_TAC) THEN
  TRY(PU_C_STORE_REJ_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(mld_rej_uniform_list b i)`) (lhs(concl th)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `tv:num` &&
    can (term_match [] `val(mld_rej_uniform_cand b i)`) (lhs(concl th)))) THEN
  fin;;
let PU_C_PATH_TAC = PU_C_PATH_GEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_C_EXPAND_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN REWRITE_TAC[LT_REFL];;
let PU_C_FIN_G_TAC = REWRITE_TAC[GSYM (ASSUME `i + 1 = G`); LT_REFL] THEN PU_C_EXPAND_TAC THEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_C_FIN_280_TAC = SUBGOAL_THEN `280 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `G = 280`] THEN ARITH_TAC; ALL_TAC] THEN PU_C_EXPAND_TAC THEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_C_LAST_TAC =
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < G`; `~(i + 1 < G)`] THEN ARITH_TAC; ALL_TAC];;
let PU_C_BODY_TAC =
  PU_C_SETUP_TAC THEN
  ASM_CASES_TAC `tv < 8380417` THEN ASM_CASES_TAC `i + 1 < G` THEN PU_IFF_TAC THENL
   [PU_C_PATH_TAC;
    PU_C_LAST_TAC THEN ASM_CASES_TAC `G = 280` THENL
     [PU_C_PATH_GEN PU_C_FIN_280_TAC;
      SUBGOAL_THEN `G < 280` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`G <= 840 DIV 3`; `~(G = 280)`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word (3 * G):int64) = 3 * G` ASSUME_TAC THENL
       [MATCH_MP_TAC PU_VAL_WORD THEN UNDISCH_TAC `G < 280` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `0 + c + 1 = 256` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
        MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `0 + c < 256`; `G <= 840 DIV 3`; `~(G = 280)`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN PU_C_PATH_GEN PU_C_FIN_G_TAC];
    PU_C_PATH_TAC;
    PU_C_LAST_TAC THEN
    SUBGOAL_THEN `G = 280` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
      MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `0 + c < 256`; `G <= 840 DIV 3`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN PU_C_PATH_GEN PU_C_FIN_280_TAC];;
let PU_C_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_SCAN1 = prove(PU_SCAN1_TM,
  CONCRETIZE_F_EVENTS_TAC PU_S1_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `fr:int64`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`256`; `0`; `b:num->byte`; `840`; `mld_rej_uniform_groups 256 0 (b:num->byte) 840`] MLD_REJ_UNIFORM_GROUPS) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `G = mld_rej_uniform_groups 256 0 (b:num->byte) 840` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_POS THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:num->byte`; `G:num`] PU_G_FACTS) THEN ANTS_TAC THENL [EXPAND_TAC "G" THEN REFL_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `G:num` `pc + mldsa_poly_uniform_loop1` `pc + mldsa_poly_uniform_loop1_exit` PU_S1_INV_G THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `0 < G` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `~(a <= j /\ j < a)`; WORD_ADD_0; ARITH_RULE `~(k < 0)`] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    PU_C_BODY_TAC;
    PU_C_EXIT_TAC]);;

(* ----- c2_stmt.ml ----- *)
let PU_SCAN2_TM = parse_term
 "exists f_events.
    forall e (a:int64) (fr:int64) (c0:num) (f:num->int32) (b:num->byte) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      c0 < 256 /\\
      nonoverlapping (a,1024) (word_add fr (word 224),168) /\\
      ALL (nonoverlapping (word pc,libmldsa_size))
          [(a,1024); (word_add fr (word 224),168)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + mldsa_poly_uniform_loop2) /\\
                read RSP s = fr /\\ read RBX s = a /\\
                read RAX s = word 3 /\\ read RSI s = word c0 /\\
                (!j. j < 168
                     ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\\
                (!k. k < c0
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = f k) /\\
                read events s = e)
           (\\s. read RIP s = word (pc + mldsa_poly_uniform_loop2_exit1) /\\
                read RSP s = fr /\\ read RBX s = a /\\
                read RSI s = word (c0 + MIN (256 - c0) (LENGTH(mld_rej_uniform_list b 56))) /\\
                (!k. k < c0 + MIN (256 - c0) (LENGTH(mld_rej_uniform_list b 56))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         (if k < c0 then f k else EL (k - c0) (mld_rej_uniform_list b 56))) /\\
                (!j. j < 168
                     ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a fr c0 b pc /\\
                   memaccess_inbounds e2
                    [a,1024; word_add fr (word 224),168]
                    [a,1024]))
           (MAYCHANGE [RIP; RAX; RCX; RDX; RSI] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(a,1024)])";;

let PU_S2_TEMPLATE =
 `\(a:int64) (fr:int64) (c0:num) (b:num->byte) (pc:num).
    APPEND (f_ev_epil a fr c0 b pc)
     (APPEND
       (ENUMERATEL (mld_rej_uniform_groups 256 c0 b 168)
         (\i. if i + 1 < mld_rej_uniform_groups 256 c0 b 168
              then if val(mld_rej_uniform_cand b i) < 8380417
                   then f_ev_a a fr c0 b pc i else f_ev_r a fr c0 b pc i
              else if mld_rej_uniform_groups 256 c0 b 168 = 56
                   then if val(mld_rej_uniform_cand b i) < 8380417
                        then f_ev_ah a fr c0 b pc i else f_ev_rh a fr c0 b pc i
                   else f_ev_af a fr c0 b pc i))
       (f_ev_prol a fr c0 b pc)):(uarch_event)list`;;

let PU_G_FACTS2 = prove(`!(b:num->byte) c G. c < 256 /\ mld_rej_uniform_groups 256 c b 168 = G
  ==> c + LENGTH(mld_rej_uniform_list b G) <= 256 /\
      c + MIN (256 - c) (LENGTH(mld_rej_uniform_list b 56)) = c + LENGTH(mld_rej_uniform_list b G) /\
      (!k. k < LENGTH(mld_rej_uniform_list b G)
           ==> EL k (mld_rej_uniform_list b 56) = EL k (mld_rej_uniform_list b G))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_GROUPS) THEN
  SUBGOAL_THEN `c + LENGTH(mld_rej_uniform_list (b:num->byte) G) <= 256` ASSUME_TAC THENL
   [ASM_CASES_TAC `G = 0` THENL
     [ASM_REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `?g. G = g + 1` STRIP_ASSUME_TAC THENL [EXISTS_TAC `G - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:num` o check (fun th -> is_forall(concl th))) THEN
      ASM_REWRITE_TAC[ARITH_RULE `g < g + 1`] THEN
      REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
      COND_CASES_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`256`; `c:num`; `b:num->byte`; `168`] MLD_REJ_UNIFORM_CTR) THEN
    REWRITE_TAC[mld_rej_uniform_ctr] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
    ASM_REWRITE_TAC[EQ_ADD_LCANCEL] THEN DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EL_MLD_REJ_UNIFORM_LIST_PREFIX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `G <= 168 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN ACCEPT_TAC]);;

(* ----- c2_setup.ml ----- *)
let PU_D_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < G`) o check (fun th -> is_forall(concl th) && can (term_match [] `!m. m < G ==> P m`) (concl th))) THEN STRIP_TAC THEN
  FULL_INIT_TAC THEN (let th = ASSUME `i < G` in RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THEN
  MAP_EVERY PU_BYTE_FACT [`0`;`1`;`2`] THEN
  SUBGOAL_THEN `read (memory :> bytes16 (word_add fr (word (224 + 3 * i)))) s0 = word_join ((b:num->byte) (3 * i + 1)) (b (3 * i))` ASSUME_TAC THENL
   [REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    SUBGOAL_THEN `word_add (word_add fr (word (224 + 3 * i))) (word 1):int64 = word_add fr (word (224 + 3 * i + 1))` ASSUME_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (3 * (i + 1)):int64) = 3 * (i + 1)` ASSUME_TAC THENL [MATCH_MP_TAC PU_VAL_WORD THEN UNDISCH_TAC `i < 168 DIV 3` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (fr:int64) (word (1 * 3 * (i + 1) + 221)) = word_add fr (word (224 + 3 * i))` ASSUME_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `word_add (fr:int64) (word (1 * 3 * (i + 1) + 223)) = word_add fr (word (224 + 3 * i + 2))` ASSUME_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_UNIFORM_GROUPS_NEXT (CONJ (ASSUME `mld_rej_uniform_groups 256 c0 (b:num->byte) 168 = G`) (ASSUME `i < G`))) THEN
  MP_TAC(ISPECL [`word_or (word_or (word_zx((b:num->byte)(3 * i))) (word_shl (word_zx(b(3 * i + 1))) 8)) (word_shl (word_zx(b(3 * i + 2))) 16):int32`; `8388607`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  REWRITE_TAC[GSYM mld_rej_uniform_cand] THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND; SAMPLING_LENGTH_COND] THEN
  ABBREV_TAC `c = LENGTH(mld_rej_uniform_list (b:num->byte) i)` THEN
  ABBREV_TAC `tv = val(mld_rej_uniform_cand (b:num->byte) i)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mld_rej_uniform_cand (b:num->byte) i = word tv` ASSUME_TAC THENL [EXPAND_TAC "tv" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  X86_STEPS_TAC PU_EXEC (1--5) THEN
  SAMPLING_REG_TAC `RCX` `word_zx(mld_rej_uniform_cand (b:num->byte) i):int64` [mld_rej_uniform_cand] THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && can (term_match [] `read c s`) (lhs(concl th)) then REWRITE_RULE [ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th else th);;



(* ----- c2_bodyx.ml ----- *)
let PU_IFF_TAC =
  FIRST_X_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `i + 1 < G` then MP_TAC th else NO_TAC) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC;;
let PU_D_STORE_TAC =
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_CASES_TAC `k < c0 + c` THENL
   [FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`] THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN (MAP_EVERY UNDISCH_TAC [`k < c0 + c`; `~(k < c0)`; `~(k - c0 < c)`] THEN ARITH_TAC));
    SUBGOAL_THEN `(k:num) = c0 + c` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(c0 + c < c0) /\ (c0 + c) - c0 = c` STRIP_ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`; ARITH_RULE `~(c < c)`; SUB_REFL; EL; HD]];;

let PU_D_STORE_REJ_TAC =
  REWRITE_TAC[ADD_CLAUSES; APPEND_NIL] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MP_TAC(SPEC `k:num` th) else NO_TAC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];;

let PU_D_HEAD = `word(pc+144576):int64` and PU_D_EXIT = `word(pc+144400):int64`;;

let PU_D_PATH_GEN fin =
  PU_RUN_TAC PU_EXEC 6 [PU_D_HEAD; PU_D_EXIT] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[WORD_VAL] THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ADD_CLAUSES] THEN NO_TAC) THEN
  TRY(PU_D_STORE_TAC THEN NO_TAC) THEN
  TRY(PU_D_STORE_REJ_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(mld_rej_uniform_list b i)`) (lhs(concl th)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `tv:num` &&
    can (term_match [] `val(mld_rej_uniform_cand b i)`) (lhs(concl th)))) THEN
  fin;;
let PU_D_PATH_TAC = PU_D_PATH_GEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_D_EXPAND_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN REWRITE_TAC[LT_REFL];;
let PU_D_FIN_G_TAC = REWRITE_TAC[GSYM (ASSUME `i + 1 = G`); LT_REFL] THEN PU_D_EXPAND_TAC THEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_D_FIN_280_TAC = SUBGOAL_THEN `56 = i + 1` (fun th -> REWRITE_TAC[th; LT_REFL]) THENL [MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `G = 56`] THEN ARITH_TAC; ALL_TAC] THEN PU_D_EXPAND_TAC THEN SAMPLING_PATH_DISCHARGE_TAC;;
let PU_D_LAST_TAC =
  SUBGOAL_THEN `i + 1 = G` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < G`; `~(i + 1 < G)`] THEN ARITH_TAC; ALL_TAC];;
let PU_D_BODY_TAC =
  PU_D_SETUP_TAC THEN
  ASM_CASES_TAC `tv < 8380417` THEN ASM_CASES_TAC `i + 1 < G` THEN PU_IFF_TAC THENL
   [PU_D_PATH_TAC;
    PU_D_LAST_TAC THEN ASM_CASES_TAC `G = 56` THENL
     [PU_D_PATH_GEN PU_D_FIN_280_TAC;
      SUBGOAL_THEN `G < 56` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`G <= 168 DIV 3`; `~(G = 56)`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `val(word (3 * G):int64) = 3 * G` ASSUME_TAC THENL
       [MATCH_MP_TAC PU_VAL_WORD THEN UNDISCH_TAC `G < 56` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `c0 + c + 1 = 256` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
        MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `c0 + c < 256`; `G <= 168 DIV 3`; `~(G = 56)`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
        ALL_TAC] THEN PU_D_PATH_GEN PU_D_FIN_G_TAC];
    PU_D_PATH_TAC;
    PU_D_LAST_TAC THEN
    SUBGOAL_THEN `G = 56` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_conj(rand(concl th)))) THEN
      MAP_EVERY UNDISCH_TAC [`i + 1 = G`; `c0 + c < 256`; `G <= 168 DIV 3`] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      ALL_TAC] THEN PU_D_PATH_GEN PU_D_FIN_280_TAC];;

(* ----- c2_proof_tail.ml ----- *)
let PU_S2_INV_G =
 `\i s. read RSP s = fr /\ read RBX s = a /\
        (i < G ==> read RAX s = word (3 * (i + 1))) /\
        read RSI s = word (c0 + LENGTH(mld_rej_uniform_list b i)) /\
        (!j. j < 168
             ==> read (memory :> bytes8 (word_add (word_add fr (word 224)) (word j))) s = b j) /\
        (!k. k < c0 + LENGTH(mld_rej_uniform_list b i)
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 (if k < c0 then f k else EL (k - c0) (mld_rej_uniform_list b i)))`;;

let PU_D_EXIT_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - c0` o check (fun th -> let has s = can (find_term (fun t -> is_const t && fst(dest_const t) = s)) (concl th) in is_forall(concl th) && has "LENGTH" && has "EL" && not(has "read") && not(has "ensures"))) THEN
    ANTS_TAC THENL [MAP_EVERY UNDISCH_TAC [`k < c0 + LENGTH (mld_rej_uniform_list b G)`; `~(k < c0)`] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_SCAN2 = prove(PU_SCAN2_TM,
  CONCRETIZE_F_EVENTS_TAC PU_S2_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `fr:int64`; `c0:num`; `f:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`256`; `c0:num`; `b:num->byte`; `168`; `mld_rej_uniform_groups 256 c0 (b:num->byte) 168`] MLD_REJ_UNIFORM_GROUPS) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `G = mld_rej_uniform_groups 256 c0 (b:num->byte) 168` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_POS THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:num->byte`; `c0:num`; `G:num`] PU_G_FACTS2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "G" THEN REFL_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `G:num` `pc + mldsa_poly_uniform_loop2` `pc + mldsa_poly_uniform_loop2_exit1` PU_S2_INV_G THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `0 < G` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH; MULT_CLAUSES; ADD_CLAUSES; ARITH_RULE `~(a <= j /\ j < a)`; WORD_ADD_0; ARITH_RULE `~(k < 0)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes32` (concl th) && free_in `f:num->int32` (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC];
    PU_D_BODY_TAC;
    PU_D_EXIT_TAC]);;

(* ----- the loop over the further blocks (PU_D) and the release (PU_E) ----- *)
let pu_stream = new_definition `pu_stream (S:1600 word) = mld_keccak_squeeze_byte 168 S 168`;;
let pu_k0 = new_definition `pu_k0 (S:1600 word) = mld_poly_uniform_nblocks (pu_stream S)`;;

let PU_D_TM = parse_term
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (a:int64) (S:1600 word) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        mld_rej_uniform_terminates (pu_stream S) /\\
        nonoverlapping (a,1024) (bq,1384) /\\
        ALLPAIRS nonoverlapping [(a,1024); (bq,1384)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + mldsa_poly_uniform_loop1_exit) /\\
                read RSP s = word_add bq (word 296) /\\ read RBX s = a /\\
                read R12 s = word 168 /\\ (read DF s <=> false) /\\
                read RSI s = word (MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280))) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> bytes (word_add bq (word 312),200)) s = val(keccak_squeeze 5 S) /\\
                (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list (pu_stream S) 280)) /\\
                read events s = e)
          (\\s. read RIP s = word (pc + mldsa_poly_uniform_join13) /\\
                read RSP s = word_add bq (word 296) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!k. k < 256
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list (pu_stream S)
                                (280 + 56 * pu_k0 S))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a S bq mc pc /\\
                   memaccess_inbounds e2
                    [a,1024; bq,1384; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [a,1024; bq,1384]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [RBX; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(bq,1384)])";;
let PU_CTR = prove(`!(s:num->byte) t. MIN 256 (LENGTH(mld_rej_uniform_list s t)) + MIN (256 - MIN 256 (LENGTH(mld_rej_uniform_list s t))) (LENGTH(mld_rej_uniform_list (\j. s(3 * t + j)) 56)) = MIN 256 (LENGTH(mld_rej_uniform_list s (t + 56)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`s:num->byte`; `t:num`; `MIN 256 (LENGTH(mld_rej_uniform_list (s:num->byte) t))`] MLD_REJ_UNIFORM_CTR_BLOCK) THEN
  REWRITE_TAC[mld_rej_uniform_ctr] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN REWRITE_TAC[]);;
let PU_CTR_I = SPECL [`pu_stream S`; `280 + 56 * i`] PU_CTR |> REWRITE_RULE[ARITH_RULE `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`];;
let PU_ELB = SPECL [`pu_stream S`; `280 + 56 * i`; `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`] MLD_REJ_UNIFORM_EL_BLOCK |> REWRITE_RULE[ARITH_RULE `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`];;

let PU_BLK = prove
 (`!(S:1600 word) m (A:int64) s:x86state.
     read (memory :> bytes(A,168)) s = val(keccak_squeeze (m + 1) S) MOD 2 EXP (8 * 168)
     ==> !j. j < 168 ==> read (memory :> bytes8 (word_add A (word j))) s = mld_keccak_squeeze_byte 168 S 168 (168 * m + j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:int64`; `168`; `1`; `keccak_squeeze m (S:1600 word)`; `s:x86state`] MLD_SQUEEZE_BLOCKS_BYTES8) THEN
  ANTS_TAC THENL [REWRITE_TAC[ONE; NSUM_CLAUSES_NUMSEG_LT; ARITH_RULE `168 * SUC 0 = 168`; MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; keccak_squeeze] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`168`; `S:1600 word`; `m:num`; `j:num`] MLD_KECCAK_SQUEEZE_BYTE_SHIFT) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC);;

let PU_D_TEMPLATE = parse_term
 "\\(a:int64) (S:1600 word) (bq:int64) (mc:int64) (pc:num).
    if pu_k0 S = 0
    then f_ev_skip a S bq mc pc
    else APPEND (f_ev_exit a S bq mc pc)
          (APPEND (ENUMERATEL (pu_k0 S)
                    (\\i. if i + 1 < pu_k0 S
                         then f_ev_c a S bq mc pc i else f_ev_l a S bq mc pc i))
                  (f_ev_enter a S bq mc pc)):(uarch_event)list";;
let PU_D_INV = `\i s. read RSP s = word_add bq (word 296) /\ read RBX s = a /\ read R12 s = word 168 /\
        (read DF s <=> false) /\
        read RSI s = word (MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))) /\
        read (memory :> bytes64 (word_add bq (word 304))) s = a /\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        read (memory :> bytes (word_add bq (word 312),200)) s = val(keccak_squeeze (5 + i) S) /\
        (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 EL k (mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`;;
let PU_SPLIT_MEMACC =
  FIRST_X_ASSUM(fun mth ->
    match strip_comb(concl mth) with
      Const("memaccess_inbounds",_),(ev::_) when is_var ev && name_of ev = "e2" ->
        FIRST_ASSUM(fun eqth ->
          if is_eq(concl eqth) && lhs(concl eqth) = ev then
            let th' = REWRITE_RULE[eqth; MEMACCESS_INBOUNDS_APPEND] mth in
            MAP_EVERY ASSUME_TAC (CONJUNCTS th')
          else NO_TAC)
    | _ -> NO_TAC);;
let PU_D_ALLOWED = [`bq:int64`; `mc:int64`; `pc:num`; `i:num`; `a:int64`; `S:1600 word`];;
let PU_ZZ = prove(`!t. t < 2 EXP 32 ==> word_zx(word_zx(word t:int64):int32):int64 = word t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  SUBGOAL_THEN `t < 2 EXP 64` (fun th -> ASM_SIMP_TAC[th; MOD_LT; MOD_LT_EQ]) THEN ASM_ARITH_TAC);;
let PU_CMP = prove(`!L. ~(MIN 256 L < 255 \/ MIN 256 L = 255) <=> 256 <= L`, GEN_TAC THEN REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;
let PU_D_BODY_TAC =
  (X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN REWRITE_TAC[APPEND_NIL] THEN PU_SPLIT_MEMACC THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)) < 256` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> (pu_k0 S) <= k`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`i < pu_k0 S`] THEN ARITH_TAC;
    ALL_TAC]) THEN (X86_STEPS_TAC PU_EXEC (1--8) THEN PU_NORM_TAC) THEN (X86_STEPS_TAC PU_EXEC (9--9) THEN PU_NORM_TAC THEN KECCAK_STATE_WBYTES_TAC `keccak_squeeze (5 + i) S`) THEN (FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PU_EXEC "H_PERM"
   [`read RDI s`; `keccak_squeeze (5 + i) S`; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PU_D_ALLOWED 10) THEN (RULE_ASSUM_TAC(REWRITE_RULE[PU_SQ_SUC]) THEN PU_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add bq (word 312))) s10:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PU_FIRST168 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC)) THEN (X86_STEPS_TAC PU_EXEC (11--20) THEN PU_NORM_TAC) THEN (LIBC_PLT_TAC PU_EXEC (layout "plt_memcpy") (layout "got_memcpy") 20) THEN (PU_LIBC_CALL_TAC "H_MEMCPY" PU_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; `val(keccak_squeeze (6 + i) S) MOD 2 EXP (8 * 168)`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] PU_D_ALLOWED 22) THEN (X86_STEPS_TAC PU_EXEC (23--31) THEN PU_NORM_TAC) THEN (FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes (word_add bq (word 520),168)) s31` with _ -> false) then ASSUME_TAC(MATCH_MP (REWRITE_RULE[ARITH_RULE `(5 + i) + 1 = 6 + i`] (SPECL [`S:1600 word`; `5 + i`; `word_add bq (word 520):int64`; `s31:x86state`] PU_BLK)) th) else NO_TAC)) THEN (SUBGOAL_THEN `!j. j < 168 ==> read (memory :> bytes8 (word_add bq (word (296 + 224 + j)))) s31 = pu_stream S (3 * (280 + 56 * i) + j)` ASSUME_TAC THENL
   [REWRITE_TAC[pu_stream] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `word_add bq (word (296 + 224 + j)):int64 = word_add (word_add bq (word 520)) (word j)` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < 168 ==> read (memory :> bytes8 (word_add A (word j))) s = f j`) (concl th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE `168 * (5 + i) + j = 3 * (280 + 56 * i) + j`];
    ALL_TAC]) THEN (SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i))) < 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  (((REMOVE_THEN "H_SCAN2" (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
   [`e:(uarch_event)list`; `a:int64`; `read RSP s`; `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`;
    `\ k. EL k (mld_rej_uniform_list (pu_stream S) (280 + 56 * i))`;
    `\ j. pu_stream S (3 * (280 + 56 * i) + j)`; `pc:num`] 32 THENL
   [ALL_TAC; LABEL_TAC "H_SCAN2" th]))) THENL [((CONJ_TAC THENL
   [MATCH_MP_TAC PU_ZZ THEN REWRITE_TAC[MIN] THEN COND_CASES_TAC THENL [CONV_TAC NUM_REDUCE_CONV; POP_ASSUM MP_TAC THEN ARITH_TAC];
    PU_E2_CORE (ref PU_D_ALLOWED)])); ALL_TAC]) THEN (RULE_ASSUM_TAC(REWRITE_RULE[PU_CTR_I]) THEN PU_NORM_TAC) THEN (SUBGOAL_THEN `256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1))) <=> ~(i + 1 < pu_k0 S)` ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[NOT_LT] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> pu_k0 S <= k`) (concl th))) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = pu_k0 S` SUBST1_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < pu_k0 S`; `~(i + 1 < pu_k0 S)`] THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC]) THEN (PU_STEP_TAC PU_EXEC 33 THEN PU_STEP_TAC PU_EXEC 34) THEN (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ARITH_RULE `5 + (i + 1) = (5 + i) + 1`] THEN REPEAT CONJ_TAC) THEN
  (REWRITE_TAC[PU_CMP; ASSUME `256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1))) <=> ~(i + 1 < pu_k0 S)`; ARITH_RULE `(5 + i) + 1 = 6 + i`] THEN
    ASM_CASES_TAC `i + 1 < pu_k0 S` THEN
    FIRST_ASSUM(fun th -> if concl th = `i + 1 < pu_k0 S` || concl th = `~(i + 1 < pu_k0 S)` then REWRITE_TAC[th] else NO_TAC) THEN
    TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        MP_TAC(SPEC `k:num` PU_ELB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> can (term_match [] `!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1)))) ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = v`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN PU_SAFETY_TAC);;

let PU_D_EXIT_TAC =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))) = 256` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))`] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))) = 256`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_D = prove(PU_D_TM,
  (REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (PU_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (PU_RENAME_E2 PU_SCAN2) "H_SCAN2" THEN
  CONCRETIZE_F_EVENTS_TAC PU_D_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `S:1600 word`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN RULE_ASSUM_TAC(REWRITE_RULE[GSYM pu_k0])) THEN
  ASM_CASES_TAC `pu_k0 S = 0` THENL
   [(FIRST_X_ASSUM(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]) THEN (SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256`]) THEN
  REWRITE_TAC[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256`]) THEN (FULL_INIT_TAC THEN PU_STEP_TAC PU_EXEC 1 THEN PU_STEP_TAC PU_EXEC 2) THEN (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC);
    REWRITE_TAC[EQF_INTRO(ASSUME `~(pu_k0 S = 0)`)] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `pu_k0 S` `pc + mldsa_poly_uniform_join7` `pc + mldsa_poly_uniform_join13` PU_D_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      (FULL_INIT_TAC THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> (pu_k0 S) <= k`) (concl th))) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (let th = ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)` in RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)) THEN (PU_STEP_TAC PU_EXEC 1 THEN PU_STEP_TAC PU_EXEC 2 THEN PU_STEP_TAC PU_EXEC 3 THEN PU_STEP_TAC PU_EXEC 4) THEN (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; DISCHARGE_SAFETY_PROPERTY_TAC]);
      PU_D_BODY_TAC;
      PU_D_EXIT_TAC]]);;

let PU_E_TM = parse_term
 "!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> exists f_events.
      forall e (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add bq (word 296)) /\\
        ALLPAIRS nonoverlapping [(bq,1384)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + mldsa_poly_uniform_join13) /\\
                read RSP s = word_add bq (word 296) /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read events s = e)
          (\\s. read RIP s = word (pc + mldsa_poly_uniform_after_memset) /\\
                read RSP s = word_add bq (word 296) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events bq mf pc /\\
                   memaccess_inbounds e2
                    [bq,1384; word(pc + got_memset),8; ea,el]
                    [bq,1384]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [RAX; RBX; RDX] ,,
           MAYCHANGE [memory :> bytes(bq,1384)])";;

let PU_E = prove(PU_E_TM,
  (REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC `\(bq:int64) (mf:int64) (pc:num). f_ev_E bq mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN (GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN FULL_INIT_TAC) THEN (VERIF_SSE_STEPS_TAC PU_EXEC (1--20) THEN PU_NORM_TAC) THEN (LIBC_PLT_TAC PU_EXEC (layout "plt_memset") (layout "got_memset") 20) THEN (PU_LIBC_CALL_TAC "H_MEMSET" PU_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] [`bq:int64`; `mf:int64`; `pc:num`] 22) THEN (RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`])) THEN (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC));;

(* ----- the whole function from the stack frame to the call of memset ----- *)
let PU_E_ALLOWED = [`a:int64`; `seed:int64`; `M:num`; `bq:int64`; `mf:int64`; `mc:int64`; `pc:num`];;
let PU_MAIN_TM = parse_term
 "!mf mc ea el ev.
    memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (a:int64) (seed:int64) (M:num) (bq:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add bq (word 296)) /\\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\\
        nonoverlapping (a,1024) (bq,1384) /\\
        ALLPAIRS nonoverlapping [(a,1024); (bq,1384)]
          [(seed,34); (word pc,libmldsa_size); (word(pc + got_memset),8);
           (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
          (\\s. bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read RIP s = word (pc + 144008) /\\
                read RSP s = word_add bq (word 296) /\\
                read RDI s = a /\\ read RSI s = seed /\\
                read (memory :> bytes(seed,34)) s = M /\\
                (read DF s <=> false) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read events s = e)
          (\\s. read RIP s = word (pc + mldsa_poly_uniform_after_memset) /\\
                read RSP s = word_add bq (word 296) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!i. i < 256
                     ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                         mld_poly_uniform M i) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a seed M mf mc bq pc /\\
                   memaccess_inbounds e2
                    [seed,34; a,1024; bq,1384; word(pc + got_memset),8;
                     word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [a,1024; bq,1384]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [RSP] ,, MAYCHANGE [RBX; R12; R13; R14; R15] ,,
           MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(bq,1384)])";;
let PU_E2_ANY allowed =
  FULL_EXISTS_E2_TAC allowed ORELSE
  (REPEAT CONJ_TAC THEN
   FIRST [PU_E2_CORE allowed; (ASM_REWRITE_TAC[] THEN NO_TAC); (CONV_TAC WORD_RULE THEN NO_TAC); (REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN NO_TAC)]);;
let PU_MCALL name ilist n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [PU_E2_ANY (ref PU_E_ALLOWED); LABEL_TAC name th]);;
let PU_STREAM_EQ = prove(`!M. pu_stream (mld_keccak_absorb_once 168 0x1F 34 M) = mld_shake128_stream 34 M`, REWRITE_TAC[pu_stream; mld_shake128_stream]);;

let PU_MAIN = prove(PU_MAIN_TM,
  (REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_B) mcp) "H_B" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_D) mcp) "H_D" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`ea:int64`;`el:num`;`ev:num`] PU_E) ms) "H_E") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PU_A "H_A" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PU_SCAN1 "H_C" THEN
  CONCRETIZE_F_EVENTS_TAC `\(a:int64) (seed:int64) (M:num) (mf:int64) (mc:int64) (bq:int64) (pc:num). f_ev_main a seed M mf mc bq pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `bq:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  (FULL_INIT_TAC) THEN
  (PU_MCALL "H_A" [`a:int64`; `seed:int64`; `M:num`; `read RSP s`; `pc:num`] 1) THEN
  (PU_NORM_TAC) THEN
  (PU_MCALL "H_B" [`a:int64`; `mld_keccak_absorb_once 168 0x1F 34 M`; `bq:int64`; `pc:num`] 2 THEN PU_NORM_TAC) THEN
  (X86_STEPS_TAC PU_EXEC (3--6) THEN PU_NORM_TAC) THEN
  (SUBGOAL_THEN `!j. j < 840 ==> read (memory :> bytes8 (word_add bq (word (296 + 224 + j)))) s6 = pu_stream (mld_keccak_absorb_once 168 0x1F 34 M) j` ASSUME_TAC THENL
   [REWRITE_TAC[pu_stream] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `word_add bq (word (296 + 224 + j)):int64 = word_add bq (word (520 + j))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < 840 ==> read (memory :> bytes8 (word_add bq (word (520 + j)))) s = f j`) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (PU_MCALL "H_C" [`a:int64`; `read RSP s`; `pu_stream (mld_keccak_absorb_once 168 0x1F 34 M)`; `pc:num`] 7 THEN PU_NORM_TAC) THEN
  (SUBGOAL_THEN `mld_rej_uniform_terminates (pu_stream (mld_keccak_absorb_once 168 0x1F 34 M))` ASSUME_TAC THENL
   [REWRITE_TAC[PU_STREAM_EQ] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  (PU_MCALL "H_D" [`a:int64`; `mld_keccak_absorb_once 168 0x1F 34 M`; `bq:int64`; `pc:num`] 8 THEN PU_NORM_TAC) THEN
  (PU_MCALL "H_E" [`bq:int64`; `pc:num`] 9 THEN PU_NORM_TAC) THEN
  (RULE_ASSUM_TAC(REWRITE_RULE[pu_k0; PU_STREAM_EQ]) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_uniform; mld_rej_uniform_poly] THEN REPEAT CONJ_TAC) THEN
  (PU_SAFETY_TAC));;
