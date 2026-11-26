(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proof of mldsa_poly_uniform of the clang 23 -O3 build, on  *)
(* the regions between the loops of inline_uniform.ml: the zeroing of the    *)
(* Keccak state and the absorbing of the seed (straight-line code), the five *)
(* squeezes of the first block (a loop of mldsa_keccakf1600_permute and      *)
(* memcpy), the loop over the further blocks, and the release of the state.  *)
(* They are stated for the aligned stack pointer sp of the function, with    *)
(* the state at sp + 16, its position at sp + 216 and the buffer for the     *)
(* output of the squeezing at sp + 224.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_uniform.ml";;

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
  let s = mk_var(sname,`:armstate`) in
  let tm = subst [s,`s0:armstate`; mk_small_numeral off,`OFF:num`]
    `read (memory :> bytes128 (word_add sp (word OFF))) s0 = word 0:int128` in
  FIRST_ASSUM(fun th ->
    if concl th = tm then
      let th1 = REWRITE_RULE PU_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let ths = map (CONV_RULE(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC ths
    else NO_TAC);;
let PU_ZLD_TAC sname sz k =
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add sp (word %d))) %s = word 0" (8*sz) k sname) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC(butlast PU_UNSPLIT |> fun _ -> [el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC]) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC];;

(*** The state after the absorbing, from its pieces ***)

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

let PU_SW = `word_or (word_zx (word M:272 word):1600 word) (word(2 EXP 272 * 31 + 2 EXP 1336 * 128))`;;
let PU_NORMC = TRY_CONV(REWRITE_CONV[PTR_ADD_G]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let PU_NORM = CONV_RULE PU_NORMC;;

(* the piece of length len at offset off from sp + 16 at the state sn *)
let PU_PIECE_THM asl sn off len =
  let sz,lem = if len = 16 then "bytes128",PU_PIECE16 else "bytes8",PU_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add sp (word %d))) %s" sz (16 + off) sn) in
  let fact = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add sp (word %d):int64" (16 + off)) in
  let s = mk_var(sn,`:armstate`) in
  let inst = SPECL [PU_SW; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

let PU_PIECES =
  [0,16; 16,16; 32,1; 33,1; 34,1] @ map (fun j -> j,1) (35--39) @
  map (fun j -> j,16) [40;56;72;88;104;120;136] @ map (fun j -> j,1) (152--167) @
  [168,16; 184,16];;

(* bytes(sp+16,200) = val Sw at the state sn, as a chain of extensions *)
let PU_CHAIN_TAC sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:armstate`) in
    let d = `word_add sp (word 16):int64` in
    let x = mk_comb(`val:1600 word->num`,PU_SW) in
    let cur0 = PU_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`]
       `read (memory :> bytes(word_add sp (word 16),0)) s = x MOD 2 EXP (8 * 0)`,
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

let PU_A_TM = parse_term
 "exists f_events.
    forall e (a:int64) (seed:int64) (M:num) (guard:int64) (canary:int64) (sp:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\ aligned 32 sp /\\
      ALLPAIRS nonoverlapping [(sp,1088)]
        [(seed,34); (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8); (guard,8)]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_adrp1) /\\
                read SP s = sp /\\
                C_ARGUMENTS [a; seed] s /\\
                read (memory :> bytes64(word(pc + got_stack_chk_guard))) s = guard /\\
                read (memory :> bytes64 guard) s = canary /\\
                read (memory :> bytes(seed,34)) s = M /\\
                read events s = e)
           (\\s. read PC s = word (pc + mldsa_poly_uniform_loop1) /\\
                read SP s = sp /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                read X23 s = word 0 /\\ read X24 s = word_add sp (word 16) /\\
                read X25 s = word 168 /\\ read X26 s = word 840 /\\
                read X27 s = word_add sp (word 224) /\\
                read (memory :> bytes(word_add sp (word 16),200)) s =
                  val(mld_keccak_absorb_once 168 0x1F 34 M) /\\
                read (memory :> bytes32(word_add sp (word 216))) s = word 168 /\\
                read (memory :> bytes64(word_add sp (word 1080))) s = canary /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a seed M guard pc sp /\\
                   memaccess_inbounds e2
                    [seed,34; sp,1088; word(pc + got_stack_chk_guard),8; guard,8]
                    [sp,1088]))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [X19; X22; X23; X24; X25; X26; X27] ,,
            MAYCHANGE [memory :> bytes(sp,1088)])";;


let PU_A_TAC =
  CONCRETIZE_F_EVENTS_TAC `\(a:int64) (seed:int64) (M:num) (guard:int64) (pc:num) (sp:int64). f_ev_a1 a seed M guard pc sp:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `guard:int64`; `canary:int64`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst PU_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN
  MP_TAC(ISPECL [`seed:int64`; `34`; `read memory (s0:armstate)`] READ_BYTES_BOUND) THEN REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME `read (memory :> bytes(seed,34)) s0 = M`] THEN DISCH_TAC THEN
  MP_TAC(MATCH_MP MLD_READ_BYTES_BYTES8 (ASSUME `read (memory :> bytes(seed,34)) s0 = M`)) THEN DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[GEN `j:num` (MP (SPECL [`M:num`;`j:num`] PU_BYTE_SUB) (ASSUME `M < 2 EXP (8 * 34)`))] th)) THEN
  MAP_EVERY (fun (sz,k) -> let th = PU_SEED_FACT sz k in ASSUME_TAC(MP th (ASSUME SEED_HYP))) [16,0; 8,16; 4,28] THEN
  MAP_EVERY PU_SEED_BYTE [24;25;26;27;32;33] THEN
  ARM_STEPS_TAC PU_EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN ARM_STEPS_TAC PU_EXEC (2--14) THEN
  PU_ZSPLIT "s14" 40 THEN PU_ZLD_TAC "s14" 4 44 THEN
  ARM_STEPS_TAC PU_EXEC (15--22) THEN
  PU_ZSPLIT "s22" 168 THEN
  ARM_STEPS_TAC PU_EXEC (23--65) THEN
  SUBGOAL_THEN `read (memory :> bytes128 (word_add sp (word 32))) s65 = word_subword (word M:272 word) (128,128)` ASSUME_TAC THENL [FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes128 (word_add sp (word 32))) s65` with _ -> false) then MP_TAC th else NO_TAC) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC WORD_BLAST; ALL_TAC] THEN
  PU_CHAIN_TAC "s65" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC;;

let PU_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

let PU_A = prove(PU_A_TM,
  PU_A_TAC THENL
   [MP_TAC(SPEC `M:num` PU_S_WORD) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PU_MODLEMMA];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The five squeezes of the first blocks: the first 168 bytes of the state   *)
(* after i + 1 permutations are the block i of the stream.                    *)
(* ------------------------------------------------------------------------- *)

let PU_FIRST168 = prove
 (`!(a:int64) (X:1600 word) s:armstate.
     read (memory :> wbytes a) s = X
     ==> read (memory :> bytes(a,168)) s = val X MOD 2 EXP (8 * 168)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[READ_BYTES_MOD] THEN CONV_TAC NUM_REDUCE_CONV);;

let PU_SQ_SUC = prove(`!(S:1600 word) i. keccak_f1600 (keccak_squeeze i S) = keccak_squeeze (i + 1) S`,
  REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

(* ------------------------------------------------------------------------- *)
(* The five squeezes of the first blocks: a loop of mldsa_keccakf1600_permute *)
(* and memcpy of 168 bytes of the state to the buffer, with the loop body as *)
(* a lemma over its iterations. fr is the lowest address of the frame (the   *)
(* stack of the callee, below the stack pointer fr + 240), which keeps the   *)
(* regions free of wraparound.                                               *)
(* ------------------------------------------------------------------------- *)

let PU_NSUM_SUC = prove(`!(f:num->num) i. nsum {j | j < i + 1} f = nsum {j | j < i} f + f i`, REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT]);;
let PU_EXTBLK = prove
 (`!(fr:int64) i (S:1600 word) s:armstate.
     read (memory :> bytes(word_add fr (word 464),168 * i)) s =
       nsum {j | j < i} (\j. 2 EXP (8 * 168 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168)) /\
     read (memory :> bytes(word_add fr (word (464 + 168 * i)),168)) s =
       val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)
     ==> read (memory :> bytes(word_add fr (word 464),168 * (i + 1))) s =
       nsum {j | j < i + 1} (\j. 2 EXP (8 * 168 * j) * val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PU_NSUM_SUC; READ_COMPONENT_COMPOSE; ARITH_RULE `168 * (i + 1) = 168 * i + 168`; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  SUBGOAL_THEN `word_add (word_add fr (word 464)) (word (168 * i)):int64 = word_add fr (word (464 + 168 * i))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[ARITH_RULE `8 * 168 * i = 8 * (168 * i)`]);;

(*** the events of a loop body of two calls: split the memory accesses into the parts ***)
let PU_SAFETY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  (CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]) THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REPEAT CONJ_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let PU_BODY_FINAL_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [MP_TAC(SPECL [`fr:int64`; `i:num`; `S:1600 word`; `s23:armstate`] PU_EXTBLK) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
         REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN PU_SAFETY_TAC];;

let PU_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let PU_E2_CORE allowed =
    CONV_TAC(LAND_CONV PU_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let PU_E2_TAC allowed =
  (CONJ_TAC THENL [CONV_TAC WORD_RULE; PU_E2_CORE allowed]) ORELSE PU_E2_CORE allowed;;
let PU_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [PU_E2_TAC (ref vars); LABEL_TAC name th]);;

let PU_CSEL = prove(`!i. i < 5 ==> (if val(word(840 - 168 * i):int64) < 168 then word(840 - 168 * i):int64 else word 168) = word 168`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let PU_NOV tm = SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL [NONOVERLAPPING_TAC; ALL_TAC];;

let PU_ARITH = prove(`!i. i < 5 ==> word_sub (word (840 - 168 * i)) (word 168):int64 = word (840 - 168 * (i + 1)) /\ (val(word_sub (word (840 - 168 * i)) (word 168):int64) = 0 <=> ~(i + 1 < 5)) /\ word_add (word 168) (word (168 * i)):int64 = word (168 * (i + 1))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let PU_B_TM = parse_term
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (a:int64) (S:1600 word) (fr:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
        ALLPAIRS nonoverlapping [(fr,1304)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_loop1) /\\
                read SP s = word_add fr (word 240) /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                read X23 s = word 0 /\\ read X24 s = word_add fr (word 256) /\\
                read X25 s = word 168 /\\ read X26 s = word 840 /\\
                read X27 s = word_add fr (word 464) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> wbytes (word_add fr (word 256))) s = S /\\
                read events s = e)
          (\\s. read PC s = word (pc + mldsa_poly_uniform_loop1_exit) /\\
                read SP s = word_add fr (word 240) /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                read X23 s = word 840 /\\ read X24 s = word_add fr (word 256) /\\
                read X25 s = word 168 /\\ read X26 s = word 0 /\\
                read X27 s = word_add fr (word 464) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> wbytes (word_add fr (word 256))) s =
                  keccak_squeeze 5 S /\\
                (!j. j < 840
                     ==> read (memory :> bytes8 (word_add (word_add fr (word 464)) (word j))) s =
                         mld_keccak_squeeze_byte 168 S 168 j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fr mc pc /\\
                   memaccess_inbounds e2
                    [fr,1304; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [fr,1304]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X20; X21; X22; X23; X26] ,,
           MAYCHANGE [memory :> bytes(fr,1304)])";;

let PU_B_INV =
 `\i s. read SP s = word_add fr (word 240) /\ read X19 s = a /\ read X22 s = word 168 /\
        read X23 s = word (168 * i) /\ read X24 s = word_add fr (word 256) /\
        read X25 s = word 168 /\ read X26 s = word (840 - 168 * i) /\
        read X27 s = word_add fr (word 464) /\
        read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        read (memory :> wbytes (word_add fr (word 256))) s = keccak_squeeze i S /\
        read (memory :> bytes(word_add fr (word 464),168 * i)) s =
          nsum {j | j < i} (\j. 2 EXP (8 * 168 * j) *
                                val(keccak_squeeze (j + 1) S) MOD 2 EXP (8 * 168))`;;


let PU_ALLOWED = [`fr:int64`; `mc:int64`; `pc:num`; `i:num`];;
let PU_CALL_TAC name ilist n = FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PU_EXEC name ilist PU_ALLOWED n;;

let PU_B_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN REWRITE_TAC[APPEND_NIL] THEN
  ARM_STEPS_TAC PU_EXEC (1--5) THEN
  PU_CALL_TAC "H_PERM" [`read X0 s`; `keccak_squeeze i S`; `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_SQ_SUC]) THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add fr (word 256))) s6:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PU_FIRST168 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  ARM_STEPS_TAC PU_EXEC (7--14) THEN RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` PU_CSEL) (ASSUME `i < 5`)]) THEN
  LIBC_PLT_TAC PU_EXEC 14 THEN
  MAP_EVERY PU_NOV [`nonoverlapping (word_add fr (word (464 + 168 * i)):int64,168) (word_add fr (word 256),200)`; `nonoverlapping (word_add fr (word (464 + 168 * i)):int64,168) (word_add (word pc) (word 327632),8)`; `nonoverlapping (word_add fr (word (464 + 168 * i)):int64,168) (word_add fr (word 464),168 * i)`] THEN
  PU_LIBC_CALL_TAC "H_MEMCPY" PU_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)`; `read X30 s`] PU_ALLOWED 19 THEN
  ARM_STEPS_TAC PU_EXEC (20--23) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `i:num` PU_ARITH) (ASSUME `i < 5`)]) THEN REWRITE_TAC[MP (SPEC `i:num` PU_ARITH) (ASSUME `i < 5`)] THEN
  ASM_CASES_TAC `i + 1 < 5` THEN ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN PU_BODY_FINAL_TAC;;

let PU_B_EXIT_TAC =
  FULL_INIT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `168 * 5 = 840`]) THEN
  CONJ_TAC THENL
   [MP_TAC(REWRITE_RULE[ARITH_RULE `168 * 5 = 840`] (SPECL [`word_add fr (word 464):int64`; `168`; `5`; `S:1600 word`; `s0:armstate`] MLD_SQUEEZE_BLOCKS_BYTES8)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ARITH_RULE `0 < 168`]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_B = prove(PU_B_TM,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC `\(fr:int64) (mc:int64) (pc:num). APPEND (f_ev_epil fr mc pc) (APPEND (ENUMERATEL 5 (\i. if i + 1 < 5 then f_ev_c fr mc pc i else f_ev_l fr mc pc i)) (f_ev_prol fr mc pc)):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `S:1600 word`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PU_EXEC] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `5` `pc + mldsa_poly_uniform_loop1` `pc + mldsa_poly_uniform_loop1_exit` PU_B_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND] THEN
    REPEAT CONJ_TAC THEN REWRITE_TAC[keccak_squeeze; NSUM_CLAUSES_NUMSEG_LT; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN TRY DISCHARGE_SAFETY_PROPERTY_TAC;
    PU_B_BODY_TAC;
    PU_B_EXIT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The loop over the further blocks (while the polynomial has fewer than 256 *)
(* coefficients): squeeze one block, copy it, sample from it with PU_SCAN2.  *)
(* ------------------------------------------------------------------------- *)

let pu_stream = new_definition `pu_stream (S:1600 word) = mld_keccak_squeeze_byte 168 S 168`;;
let pu_k0 = new_definition `pu_k0 (S:1600 word) = mld_poly_uniform_nblocks (pu_stream S)`;;

let PU_D_TM = parse_term
 "!mc ea el ev.
    memcpy_full_contract mc ea el ev
    ==> exists f_events.
      forall e (a:int64) (S:1600 word) (fr:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
        mld_rej_uniform_terminates (pu_stream S) /\\
        nonoverlapping (a,1024) (fr,1304) /\\
        ALLPAIRS nonoverlapping [(a,1024); (fr,1304)]
          [(word pc,libmldsa_size); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_loop2_exit) /\\
                read SP s = word_add fr (word 240) /\\ read X19 s = a /\\ read X22 s = word 168 /\\
                read X23 s = word 8380417 /\\
                read X24 s = word (MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280))) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read (memory :> wbytes (word_add fr (word 256))) s = keccak_squeeze 5 S /\\
                (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280))
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list (pu_stream S) 280)) /\\
                read events s = e)
          (\\s. read PC s = word (pc + mldsa_poly_uniform_loop3_exit) /\\
                read SP s = word_add fr (word 240) /\\
                read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (!k. k < 256
                     ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                         EL k (mld_rej_uniform_list (pu_stream S)
                                (280 + 56 * pu_k0 S))) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events a S fr mc pc /\\
                   memaccess_inbounds e2
                    [a,1024; fr,1304; word(pc + got_memcpy),8; ea,el;
                     word(pc + rodata_mld_KeccakF_RoundConstants),192]
                    [a,1024; fr,1304]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
           MAYCHANGE [memory :> bytes(a,1024); memory :> bytes(fr,1304)])";;

let PU_ALLOWED = [`fr:int64`; `mc:int64`; `pc:num`; `i:num`; `a:int64`; `S:1600 word`];;
let PU_CMP255 = prove(`!c. c <= 256 ==> ((255 <= val(word c:int64) /\ ~(val(word_sub (word c:int64) (word 255)) = 0)) <=> 255 < c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word c:int64) = c` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `(word c:int64) = word 255 <=> c = 255` SUBST1_TAC THENL
   [EQ_TAC THENL [DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN ASM_REWRITE_TAC[] THEN
                  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV;
                  DISCH_THEN SUBST1_TAC THEN REFL_TAC]; ALL_TAC] THEN ARITH_TAC);;

let PU_BLK = prove
 (`!(S:1600 word) m (A:int64) s:armstate.
     read (memory :> bytes(A,168)) s = val(keccak_squeeze (m + 1) S) MOD 2 EXP (8 * 168)
     ==> !j. j < 168 ==> read (memory :> bytes8 (word_add A (word j))) s = mld_keccak_squeeze_byte 168 S 168 (168 * m + j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`A:int64`; `168`; `1`; `keccak_squeeze m (S:1600 word)`; `s:armstate`] MLD_SQUEEZE_BLOCKS_BYTES8) THEN
  ANTS_TAC THENL [REWRITE_TAC[ONE; NSUM_CLAUSES_NUMSEG_LT; ARITH_RULE `168 * SUC 0 = 168`; MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; keccak_squeeze] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`168`; `S:1600 word`; `m:num`; `j:num`] MLD_KECCAK_SQUEEZE_BYTE_SHIFT) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN ACCEPT_TAC);;

let PU_LEFTASSOC_CONV = TRY_CONV(CONS_TO_APPEND_CONV) THENC REWRITE_CONV[APPEND_ASSOC];;
let PU_E2_CORE allowed =
    CONV_TAC(LAND_CONV PU_LEFTASSOC_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SAFE_UNIFY_REFL_TAC allowed (ref ["f_events_callee"; "f_ev_"]);;
let PU_E2_TAC allowed =
  (CONJ_TAC THENL [FIRST [REFL_TAC; CONV_TAC WORD_RULE; ASM_REWRITE_TAC[] THEN NO_TAC]; PU_E2_CORE allowed]) ORELSE PU_E2_CORE allowed;;
let PU_LIBC_CALL_TAC name execth ilist vars n =
  REMOVE_THEN name (fun th ->
    LIBC_CONTRACT_SIM_TAC ~is_safety_thm:true execth th ilist n THENL
     [PU_E2_TAC (ref vars); LABEL_TAC name th]);;
let PU_NOV tm = SUBGOAL_THEN tm (fun th -> ASSUME_TAC th THEN ASSUME_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES] th)) THENL [NONOVERLAPPING_TAC; ALL_TAC];;

let PU_CALL2_TAC name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) (`e:(uarch_event)list`::ilist) n THENL
     [PU_E2_TAC (ref PU_ALLOWED); LABEL_TAC name th]);;

let PU_CTR = prove(`!(s:num->byte) t. MIN 256 (LENGTH(mld_rej_uniform_list s t)) + MIN (256 - MIN 256 (LENGTH(mld_rej_uniform_list s t))) (LENGTH(mld_rej_uniform_list (\j. s(3 * t + j)) 56)) = MIN 256 (LENGTH(mld_rej_uniform_list s (t + 56)))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`s:num->byte`; `t:num`; `MIN 256 (LENGTH(mld_rej_uniform_list (s:num->byte) t))`] MLD_REJ_UNIFORM_CTR_BLOCK) THEN
  REWRITE_TAC[mld_rej_uniform_ctr] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN REWRITE_TAC[]);;
let PU_CTR_I = SPECL [`pu_stream S`; `280 + 56 * i`] PU_CTR |> REWRITE_RULE[ARITH_RULE `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`];;

let PU_LS_TAC =
  SUBGOAL_THEN `256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1))) <=> ~(i + 1 < pu_k0 S)` ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[NOT_LT] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> pu_k0 S <= k`) (concl th))) THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = pu_k0 S` SUBST1_TAC THENL [MAP_EVERY UNDISCH_TAC [`i < pu_k0 S`; `~(i + 1 < pu_k0 S)`] THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

let PU_CALL_TAC name ilist n = FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc PU_EXEC name ilist PU_ALLOWED n;;
let PU_ELB = SPECL [`pu_stream S`; `280 + 56 * i`; `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`] MLD_REJ_UNIFORM_EL_BLOCK |> REWRITE_RULE[ARITH_RULE `(280 + 56 * i) + 56 = 280 + 56 * (i + 1)`];;

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

let PU_D_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN FULL_INIT_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN REWRITE_TAC[APPEND_NIL] THEN PU_SPLIT_MEMACC THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)) < 256` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> (pu_k0 S) <= k`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC [`i < pu_k0 S`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ARM_STEPS_TAC PU_EXEC (1--8) THEN
  PU_CALL_TAC "H_PERM" [`read X0 s`; `keccak_squeeze (5 + i) S`; `pc:num`; `read SP s`; `read X30 s`] 9 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_SQ_SUC]) THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> wbytes (word_add fr (word 256))) s9:1600 word` with _ -> false) then ASSUME_TAC(MATCH_MP PU_FIRST168 th) THEN ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  ARM_STEPS_TAC PU_EXEC (10--17) THEN
  LIBC_PLT_TAC PU_EXEC 17 THEN
  MAP_EVERY PU_NOV [`nonoverlapping (word_add fr (word 464):int64,168) (word_add fr (word 256),200)`; `nonoverlapping (word_add fr (word 464):int64,168) (word_add (word pc) (word 327632),8)`; `nonoverlapping (word_add fr (word 464):int64,168) (a,1024)`; `nonoverlapping (word_add fr (word 464):int64,168) (word_add fr (word 248),8)`] THEN
  PU_LIBC_CALL_TAC "H_MEMCPY" PU_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `val(keccak_squeeze ((5 + i) + 1) S) MOD 2 EXP (8 * 168)`; `read X30 s`] PU_ALLOWED 22 THEN
  ARM_STEPS_TAC PU_EXEC (23--26) THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `read (memory :> bytes(word_add fr (word 464),168)) s26` with _ -> false) then ASSUME_TAC(MATCH_MP (SPECL [`S:1600 word`; `5 + i`; `word_add fr (word 464):int64`; `s26:armstate`] PU_BLK) th) else NO_TAC) THEN
  SUBGOAL_THEN `!j. j < 168 ==> read (memory :> bytes8 (word_add (word_add fr (word 464)) (word j))) s26 = (\j. pu_stream S (3 * (280 + 56 * i) + j)) j` ASSUME_TAC THENL
   [REWRITE_TAC[pu_stream] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < 168 ==> read (memory :> bytes8 (word_add A (word j))) s = f j`) (concl th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE `168 * (5 + i) + j = 3 * (280 + 56 * i) + j`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j < 168 ==> read (memory :> bytes8 (word_add (word_add fr (word 240)) (word (224 + j)))) s26 = pu_stream S (3 * (280 + 56 * i) + j)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `word_add (word_add fr (word 240)) (word (224 + j)):int64 = word_add (word_add fr (word 464)) (word j)` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < 168 ==> read (memory :> bytes8 (word_add (word_add fr (word 464)) (word j))) s26 = f j`) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i))) < 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  PU_CALL2_TAC "H_SCAN2" [`a:int64`; `word_add fr (word 240):int64`; `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`; `\k. EL k (mld_rej_uniform_list (pu_stream S) (280 + 56 * i))`; `\j. pu_stream S (3 * (280 + 56 * i) + j)`; `pc:num`] 27 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PU_CTR_I]) THEN
  ARM_STEPS_TAC PU_EXEC (28--29) THEN
  PU_LS_TAC THEN
  MP_TAC(SPEC `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1))))` PU_CMP255) THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `255 < MIN 256 x <=> 256 <= x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1))) <=> ~(i + 1 < pu_k0 S)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600; ARITH_RULE `5 + (i + 1) = (5 + i) + 1`] THEN REPEAT CONJ_TAC THEN
  ASM_CASES_TAC `i + 1 < pu_k0 S` THEN ASM_REWRITE_TAC[] THEN
  TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MP_TAC(SPEC `k:num` PU_ELB) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th -> can (term_match [] `!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * (i + 1)))) ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = (if k < c then f k else g k)`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN PU_SAFETY_TAC;;

let PU_D_INV = `\i s. read SP s = word_add fr (word 240) /\ read X22 s = word 168 /\
        read X23 s = word 8380417 /\
        read X24 s = word (MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))) /\
        read X25 s = word_add fr (word 464) /\ read X26 s = word 168 /\
        read X27 s = word_add fr (word 256) /\
        read (memory :> bytes64 (word_add fr (word 248))) s = a /\
        read (memory :> bytes64(word_add (word pc) (word got_memcpy))) s = mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        read (memory :> wbytes (word_add fr (word 256))) s = keccak_squeeze (5 + i) S /\
        (!k. k < MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))
             ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                 EL k (mld_rej_uniform_list (pu_stream S) (280 + 56 * i)))`;;

let PU_D_TEMPLATE = parse_term
 "\\(a:int64) (S:1600 word) (fr:int64) (mc:int64) (pc:num).
    if pu_k0 S = 0
    then f_ev_skip a S fr mc pc
    else APPEND (f_ev_exit a S fr mc pc)
          (APPEND (ENUMERATEL (pu_k0 S)
                    (\\i. if i + 1 < pu_k0 S
                         then f_ev_c a S fr mc pc i else f_ev_l a S fr mc pc i))
                  (f_ev_enter a S fr mc pc)):(uarch_event)list";;

let PU_D_INIT_TAC =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> can (term_match [] `!k. 256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * k)) ==> (pu_k0 S) <= k`) (concl th))) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)`]) THEN REWRITE_TAC[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC PU_EXEC (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MP (SPEC `LENGTH(mld_rej_uniform_list (pu_stream S) 280)` PU_CMP255) (ARITH_RULE `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256 ==> LENGTH(mld_rej_uniform_list (pu_stream S) 280) <= 256` |> fun th -> MP th (ASSUME `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256`)); ARITH_RULE `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256 ==> ~(255 < LENGTH(mld_rej_uniform_list (pu_stream S) 280))` |> fun th -> EQF_INTRO(MP th (ASSUME `LENGTH(mld_rej_uniform_list (pu_stream S) 280) < 256`))]) THEN
  ARM_STEPS_TAC PU_EXEC (3--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 ENUMERATEL; CONJUNCT1 APPEND; READ_MEMORY_WBYTES_1600] THEN REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         AP_TERM_TAC THEN ASM_ARITH_TAC;
         SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = LENGTH(mld_rej_uniform_list (pu_stream S) 280)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

let PU_D_EXIT_TAC =
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))) = 256` ASSUME_TAC THENL [MAP_EVERY UNDISCH_TAC [`256 <= LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))`] THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) (280 + 56 * pu_k0 S))) = 256`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_D_ZERO_TAC =
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256`]) THEN REWRITE_TAC[ASSUME `MIN 256 (LENGTH(mld_rej_uniform_list (pu_stream S) 280)) = 256`] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC PU_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let PU_D = prove(PU_D_TM,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memcpy_full_contract] th) "H_MEMCPY") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600 "H_PERM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PU_SCAN2 "H_SCAN2" THEN
  CONCRETIZE_F_EVENTS_TAC PU_D_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `S:1600 word`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PU_EXEC] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM pu_k0]) THEN
  ASM_CASES_TAC `pu_k0 S = 0` THENL
   [PU_D_ZERO_TAC;
    REWRITE_TAC[EQF_INTRO(ASSUME `~(pu_k0 S = 0)`)] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `pu_k0 S` `pc + mldsa_poly_uniform_loop3` `pc + mldsa_poly_uniform_loop3_exit` PU_D_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; PU_D_INIT_TAC; PU_D_BODY_TAC; PU_D_EXIT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The release of the state: zero the state and the buffer.                  *)
(* ------------------------------------------------------------------------- *)

let PU_E_TM = parse_term
 "!mf ea el ev.
    memset_full_contract mf ea el ev
    ==> exists f_events.
      forall e (fr:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 (word_add fr (word 240)) /\\
        ALLPAIRS nonoverlapping [(fr,1304)]
          [(word pc,libmldsa_size); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
          (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + mldsa_poly_uniform_loop3_exit) /\\
                read SP s = word_add fr (word 240) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                read events s = e)
          (\\s. read PC s = word (pc + mldsa_poly_uniform_after_memset) /\\
                read SP s = word_add fr (word 240) /\\
                read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                read (memory :> bytes(ea,el)) s = ev /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fr mf pc /\\
                   memaccess_inbounds e2
                    [fr,1304; word(pc + got_memset),8; ea,el]
                    [fr,1304]))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [X19] ,,
           MAYCHANGE [memory :> bytes(fr,1304)])";;

let PU_E = prove(PU_E_TM,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC `\(fr:int64) (mf:int64) (pc:num). f_ev_E fr mf pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PU_EXEC] th)) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC PU_EXEC (1--14) THEN
  LIBC_PLT_TAC PU_EXEC 14 THEN
  PU_NOV `nonoverlapping (word_add fr (word 464):int64,840) (ea,el)` THEN
  PU_LIBC_CALL_TAC "H_MEMSET" PU_EXEC [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] [`fr:int64`; `mf:int64`; `pc:num`] 19 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole function from the realignment of the stack pointer to the end  *)
(* of the release of the state: the five stages in sequence, and the        *)
(* polynomial as mld_poly_uniform of the seed.                              *)
(* ------------------------------------------------------------------------- *)

let PU_MAIN_TM = parse_term
 "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e a seed M guard canary fp pc fr.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\ aligned 32 (word_add fr (word 240)) /\\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\\
          nonoverlapping (a,1024) (fr,1328) /\\
          ALLPAIRS nonoverlapping
           [(a,1024); (fr,1328)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                    read PC s = word (pc + mldsa_poly_uniform_adrp1) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    C_ARGUMENTS [a; seed] s /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read (memory :> bytes(seed,34)) s = M /\\
                    read events s = e)
               (\\s. read PC s = word (pc + mldsa_poly_uniform_after_memset) /\\
                    read SP s = word_add fr (word 240) /\\ read X29 s = fp /\\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\\
                    read (memory :> bytes64 guard) s = canary /\\
                    read (memory :> bytes64(word_add fr (word 1320))) s = canary /\\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s = mld_poly_uniform M i) /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events a seed M guard mf mc pc fr /\\
                       memaccess_inbounds e2
                        [seed,34; a,1024; fr,1328;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; fr,1328]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(fr,1328)])";;

let PU_STREAM_EQ = prove(`!M. pu_stream (mld_keccak_absorb_once 168 0x1F 34 M) = mld_shake128_stream 34 M`,
  REWRITE_TAC[pu_stream; mld_shake128_stream]);;

let MAIN_ALLOWED = [`a:int64`; `seed:int64`; `M:num`; `guard:int64`; `mf:int64`; `mc:int64`; `pc:num`; `fr:int64`];;
let MAIN_CALL name ilist n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,PU_EXEC,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th) (`e:(uarch_event)list`::ilist) n THENL
     [(FULL_EXISTS_E2_TAC (ref MAIN_ALLOWED) ORELSE PU_E2_TAC (ref MAIN_ALLOWED)); LABEL_TAC name th]);;

let PU_MAIN = prove(PU_MAIN_TM,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_B) mcp) "H_B" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] PU_D) mcp) "H_D" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MP (SPECL [`mf:int64`;`ea:int64`;`el:num`;`ev:num`] PU_E) ms) "H_E") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PU_A "H_A" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC PU_SCAN1 "H_C" THEN
  CONCRETIZE_F_EVENTS_TAC `\(a:int64) (seed:int64) (M:num) (guard:int64) (mf:int64) (mc:int64) (pc:num) (fr:int64). f_ev_main a seed M guard mf mc pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `seed:int64`; `M:num`; `guard:int64`; `canary:int64`; `fp:int64`; `pc:num`; `fr:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst PU_EXEC] th)) THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD])) [`got_stack_chk_guard:num`; `got_memset:num`; `got_memcpy:num`] THEN
  FULL_INIT_TAC THEN
  MAIN_CALL "H_A" [`a:int64`; `seed:int64`; `M:num`; `guard:int64`; `canary:int64`; `word_add fr (word 240):int64`; `pc:num`] 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]) THEN
  MAIN_CALL "H_B" [`a:int64`; `mld_keccak_absorb_once 168 0x1F 34 M`; `fr:int64`; `pc:num`] 2 THEN
  SUBGOAL_THEN `!j. j < 840 ==> read (memory :> bytes8 (word_add (word_add fr (word 240)) (word (224 + j)))) s2 = mld_keccak_squeeze_byte 168 (mld_keccak_absorb_once 168 0x1F 34 M) 168 j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN `word_add (word_add fr (word 240)) (word (224 + j)):int64 = word_add fr (word (464 + j))` SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < 840 ==> read (memory :> bytes8 (word_add fr (word (464 + j)))) s2 = f j`) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  MAIN_CALL "H_C" [`a:int64`; `word_add fr (word 240):int64`; `mld_keccak_squeeze_byte 168 (mld_keccak_absorb_once 168 0x1F 34 M) 168`; `pc:num`] 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM PU_STREAM_EQ; GSYM pu_stream]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600]) THEN
  MAP_EVERY PU_NOV [`nonoverlapping (a:int64,1024) (fr:int64,1304)`; `nonoverlapping (fr:int64,1304) (word pc:int64,libmldsa_size)`; `nonoverlapping (fr:int64,1304) (word_add (word pc) (word 327632):int64,8)`; `nonoverlapping (fr:int64,1304) (ea:int64,el)`] THEN
  MAIN_CALL "H_D" [`a:int64`; `mld_keccak_absorb_once 168 0x1F 34 M`; `fr:int64`; `pc:num`] 4 THEN
  MAP_EVERY PU_NOV [`nonoverlapping (fr:int64,1304) (word_add (word pc) (word 327656):int64,8)`] THEN
  MAIN_CALL "H_E" [`fr:int64`; `pc:num`] 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pu_k0; PU_STREAM_EQ]) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[mld_poly_uniform; mld_rej_uniform_poly] THEN REPEAT CONJ_TAC THEN
  PU_SAFETY_TAC);;
