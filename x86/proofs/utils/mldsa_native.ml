(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa-native's x86-64 compiled code that do not   *)
(* depend on the build. These are the tools of the AArch64 proofs in         *)
(* arm/proofs/utils/mldsa_native.ml that are not about the AArch64 model,    *)
(* and the tools of the x86-64 proofs of mlkem-native for the alignment and  *)
(* the addresses of the operands of SSE instructions.                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(* ------------------------------------------------------------------------- *)
(* Reasoning about 32-bit operations on small numbers, which the compiled    *)
(* code uses for loop counters and indices, and about the flags set when     *)
(* they or pointers with the same base are compared.                         *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_64_32_SMALL = prove
 (`!n. n < 4294967296 ==> word_zx(word n:int64):int32 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_64] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_CMP_32_FLAGS = prove
 (`!x y. x < 4294967296 /\ y < 4294967296
         ==> ((&(val(word x:int32)) - &(val(word y:int32)):int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (&(val(word x:int32)) - &y:int =
               &(val(word_sub (word x) (word y):int32)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int32) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int32) = x /\ val(word y:int32) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let WORD_CMP_64_FLAGS = prove
 (`!x y. x < 18446744073709551616 /\ y < 18446744073709551616
         ==> ((&(val(word x:int64)) - &(val(word y:int64)):int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int64) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word y:int64) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(*** Replace 32-bit views of small numbers in assumptions and goal ***)

let W32_SMALL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `word_zx(word n:int64):int32`))
      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) tms);;

(*** Decide the carry and zero flags where they are arithmetic facts ***)

let DECIDE_FLAG_TAC p =
  (SUBGOAL_THEN p (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th])) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg p)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th])) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

let DECIDE_FLAGS_TAC =
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(DECIDE_FLAG_TAC p)) ps);;

(*** Express the flags in terms of the numbers compared and decide them ***)

let CMP_FLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      MP_TAC(SPECL [x;y] th) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms) THEN
  DECIDE_FLAGS_TAC;;

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

let PTR_DECIDE_FLAGS_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int64` WORD_CMP_64_FLAGS;;

(*** Prove equations between words formed from small numbers ***)

let MOD_LT_ASM_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    let t = hd(sort free_in tms) in
    MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC]);;

let WORD_ADD_LCANCEL_EQ = prove
 (`!a x y:N word. word_add a x = word_add a y <=> x = y`,
  MESON_TAC[WORD_RULE `word_sub (word_add a x) a:N word = x`]);;

let WORD_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(MOD_LT_ASM_TAC ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;
(* ------------------------------------------------------------------------- *)
(* Simplify the lanes of SIMD registers after a step, as SIMD_SIMPLIFY_CONV  *)
(* and SIMD_SIMPLIFY_TAC in common/mlkem_mldsa.ml do (copied here so as not  *)
(* to load that file).                                                       *)
(* ------------------------------------------------------------------------- *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let x86_simdable =
    can (term_match [] `read X (s:x86state):int256 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (x86_simdable o concl)));;

(* ------------------------------------------------------------------------- *)
(* Splitting off the 4 coefficients of type int32 handled by one iteration   *)
(* of a loop over a polynomial that the compiler has vectorized, as the      *)
(* CHUNK8 lemmas of utils/mlkem_native.ml do for 8 of type int16.            *)
(* ------------------------------------------------------------------------- *)

let CHUNK4_INPUT_SPLIT = prove
 (`!P i. i < 64
         ==> ((!j. 4 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 4 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 4 ==> P(4 * i + k)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `4 * (i + 1) <= j` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 4 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `4 * i <= j ==> 4 * i + (j - 4 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK4_OUTPUT_SPLIT = prove
 (`!P i. (!j. j < 4 * (i + 1) ==> P j) <=>
         (!j. j < 4 * i ==> P j) /\ (!k. k < 4 ==> P(4 * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < 4 * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 4 * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < 4 * i) ==> 4 * i + (j - 4 * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CHUNK4_ADDR = prove
 (`!a i k. word_add a (word(4 * (4 * i + k))):int64 =
           word_add (word_add a (word(16 * i))) (word(4 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The same for loops that handle one coefficient per iteration ***)

let ONE_INPUT_SPLIT = prove
 (`!P i n. (!j. i <= j /\ j < n ==> P j) <=>
           (i < n ==> P i) /\ (!j. i + 1 <= j /\ j < n ==> P j)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `j:num = i` THENL
     [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let ONE_OUTPUT_SPLIT = prove
 (`!P i. (!j. j < i + 1 ==> P j) <=> (!j. j < i ==> P j) /\ P i`,
  REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Decide the test at the end of an iteration of a loop over the             *)
(* polynomials, which compares a pointer with its final value, both offsets  *)
(* from the same base, after the conditional jump. This evaluates the        *)
(* condition in the resulting instruction pointer and in the events.         *)
(* ------------------------------------------------------------------------- *)

let PTR_DECIDE_RIP_TAC =
  let wth = WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y` in
  let pat = `val(word_sub (word_add a x) (word_add a y):int64) = 0` in
  let is_test t =
    let t' = if is_neg t then rand t else t in
    can (term_match [] pat) t' in
  let tconv = REWRITE_CONV[wth] THENC WORD_REDUCE_CONV THENC
              NUM_REDUCE_CONV in
  let conv t =
    if is_cond t && is_test(lhand(rator t)) then
      (RATOR_CONV(LAND_CONV tconv) THENC REWRITE_CONV[]) t
    else failwith "PTR_DECIDE_RIP_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (can conv)) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV conv) th else th);;

(* ------------------------------------------------------------------------- *)
(* ALIGNED_OFFSETS_TAC a k [n1; ...] adds aligned k (word_add a (word ni))   *)
(* to the assumptions for each ni, a multiple of k, given aligned k a there, *)
(* e.g. for the polynomials of an aligned vector.                            *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_OFFSETS_TAC a k ns =
  MAP_EVERY (fun n ->
    let tm = list_mk_comb(`aligned:num->int64->bool`,
       [mk_small_numeral k;
        mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                mk_comb(`word:num->int64`,mk_small_numeral n))]) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) ns;;

(* ------------------------------------------------------------------------- *)
(* For a vector instruction with a memory operand at base + index, the       *)
(* address is computed as word_add a (word(1 * n)) when the index register   *)
(* is word n, so INDEX_ADDR_TAC restates the assumptions about the 128-bit   *)
(* words at word_add a (word(16 * i)), and their alignment, in that form.    *)
(* ------------------------------------------------------------------------- *)

let INDEX_ADDR_TAC =
  let pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes128 (word_add a (word(16 * i)))) s = v`) c ||
       can (term_match [] `aligned 16 (word_add a (word(16 * i)):int64)`) c
    then ONCE_REWRITE_RULE[pth] th else th);;

(* ------------------------------------------------------------------------- *)
(* 32-bit values that the compiled code computes in 64-bit registers.        *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_ZX_32_64_32 = prove
 (`!x:int32. word_zx(word_zx x:int64):int32 = x`,
  CONV_TAC WORD_BLAST);;

let WORD_ZX_ZX_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word_zx(word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n`
   (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;
(*** The masks as conditionals ***)

let WORD_ISHR_31_COND = prove
 (`!w:int32. word_ishr w 31 =
             if ival w < &0 then word 4294967295 else word 0`,
  REWRITE_TAC[GSYM MSB_IVAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Use an "ensures" theorem about part of the code to prove a goal with a    *)
(* stronger precondition, weaker postcondition and larger frame.             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WEAKEN_TAC =
  let pth = prove
   (`!P Q C P' Q' C'.
        ensures step P Q C /\
        (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ C subsumed C'
        ==> ensures (step:A->A->bool) P' Q' C'`,
    REWRITE_TAC[subsumed] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_PRECONDITION_THM_GEN THEN
    EXISTS_TAC `P:A->bool` THEN EXISTS_TAC `C:A->A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
    EXISTS_TAC `Q:A->bool` THEN ASM_REWRITE_TAC[]) in
  fun th ->
    match snd(strip_comb(concl th)) with
      [_;p;q;c] -> MATCH_MP_TAC pth THEN MAP_EVERY EXISTS_TAC [p;q;c] THEN
                   CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]
    | _ -> failwith "ENSURES_WEAKEN_TAC";;

(*** Use an events lemma at a point where events have accumulated: given
 *** a goal with precondition including
 ***   exists e2. read events s = APPEND e2 e /\ e2 = X /\
 ***              memaccess_inbounds e2 R W
 *** and a function mk taking the term `APPEND X e` to an instance of the
 *** lemma, with that as its initial events, apply the lemma.
 ***)

let EVENTS_LEMMA_TAC (mk:term->thm) =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  W(fun (asl,w) ->
    let pre = rand(rator(rator w)) in
    let ex = find_term (fun t -> is_exists t &&
                          name_of(fst(dest_exists t)) = "e2") pre in
    let c1,c2,c3 = match conjuncts(snd(dest_exists ex)) with
                     [c1;c2;c3] -> c1,c2,c3
                   | _ -> failwith "EVENTS_LEMMA_TAC" in
    let x = rand c2 and e0 = rand(rand c1) in
    let ib = subst [x,fst(dest_exists ex)] c3 in
    let th = CONV_RULE NUM_REDUCE_CONV (mk (list_mk_icomb "APPEND" [x;e0])) in
    ASM_CASES_TAC ib THENL
     [MP_TAC th THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN ENSURES_WEAKEN_TAC] THEN
      REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REPEAT CONJ_TAC THEN TRY(AP_TERM_TAC THEN ARITH_TAC) THEN
        W(fun (asl,w) ->
          EXISTS_TAC(rand(hd(tl(conjuncts(snd(dest_exists w))))))) THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[GSYM APPEND_ASSOC];
          ONCE_REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN ASM_REWRITE_TAC[]];
        (REWRITE_TAC[subsumed] THEN NO_TAC) ORELSE
        (REWRITE_TAC[SOME_FLAGS;
                     MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
         SUBSUMED_MAYCHANGE_TAC)];
      REWRITE_TAC[ensures] THEN GEN_TAC THEN REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_MESON_TAC[]]);;
