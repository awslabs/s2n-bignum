(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa-native's compiled code that do not depend   *)
(* on the build. The tactics for flags, small 32-bit numbers and ensures     *)
(* goals are those of utils/mlkem_native.ml, which is not loaded here since  *)
(* it loads common/mlkem_mldsa.ml, which the mldsa-native proofs do not      *)
(* need.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

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

(*** The index used in a load with a UXTW register offset ***)

let VAL_WORD_ZX_UXTW = prove
 (`!n. n < 4294967296
       ==> val(word_zx(word_zx(word_zx(word n:int64):int32):int32):int64) =
           n /\
           val(word_zx(word_zx(word n:int64):int32):int64) = n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT MOD_LT_ASM_TAC THEN REWRITE_TAC[]);;

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
  let arm_simdable =
    can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (arm_simdable o concl)));;

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
(* The body of a loop that the compiler has vectorized, handling the four    *)
(* coefficients 4 * i, ..., 4 * i + 3 of some polynomials in iteration i     *)
(* with one 128-bit load or store for each. The invariant of such a loop     *)
(* states, for each polynomial x at a that the loop reads, either            *)
(*                                                                           *)
(*   !j. 4 * i <= j /\ j < 256                                               *)
(*       ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j       *)
(*                                                                           *)
(* if the loop overwrites it, or the same for j < 256 if it does not.        *)
(* VEC4_LOOP_BODY_TAC exec n, at the start of the body (after                *)
(* ENSURES_INIT_TAC "s0"), takes the four coefficients of each such          *)
(* polynomial as one 128-bit value, simulates n instructions, simplifying    *)
(* the lanes of each result, and splits each 128-bit store at an address     *)
(* word_add a (word(16 * i)) into four 32-bit values again. A fact for the   *)
(* coefficients from 4 * (i + 1) on is kept for each overwritten input.      *)
(* ------------------------------------------------------------------------- *)

let VEC4_LOOP_BODY_TAC =
  let pat_rw = `!j. 4 * i <= j /\ j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_ro = `!j. j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_lane0 = `read (memory :> bytes32 (word_add a (word(16 * i)))) s0`
  and pat_store = `read (memory :> bytes128 (word_add a (word(16 * i)))) s = x`
  and merge_tm = `read (memory :> bytes128 A) s0`
  and a_tm = `A:int64` and j_tm = `j:num` and k_tm = `k:num`
  and j4_tm = `4 * i + k` and k4_tm = `k < 4` in
  let lanes_tac =
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC in
  let split_rw th =
    MP_TAC(GEN_REWRITE_RULE I
            [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)] th) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN lanes_tac
  and split_ro th =
    let eqn = rand(snd(dest_forall(concl th))) in
    let t = mk_forall(k_tm,mk_imp(k4_tm,subst [j4_tm,j_tm] eqn)) in
    SUBGOAL_THEN t MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_ARITH_TAC;
      lanes_tac] in
  fun execth n ->
    W(fun (asl,w) ->
      let rws = filter (can (term_match [] pat_rw) o concl o snd) asl
      and ros = filter (can (term_match [] pat_ro) o concl o snd) asl in
      MAP_EVERY (fun (_,th) -> UNDISCH_THEN (concl th) split_rw) rws THEN
      MAP_EVERY (fun (_,th) -> split_ro th) ros) THEN
    W(fun (asl,w) ->
      let addrs = setify (mapfilter (fun (_,th) ->
        let l = lhand(concl th) in
        if can (term_match [] pat_lane0) l then rand(rand(rand(rator l)))
        else failwith "") asl) in
      MAP_EVERY (fun a ->
        MP_TAC(READ_MEMORY_MERGE_CONV 2 (subst [a,a_tm] merge_tm))) addrs) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC execth [k] THEN SIMD_SIMPLIFY_TAC[]) (1--n) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] pat_store) (concl th) &&
                       not(free_in `s0:armstate` (concl th)))));;

(*** After the final state of such a loop body: the invariant for i + 1 ***)

let VEC4_LOOP_FINAL_TAC lanes =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC lanes;;

(*** The loop-back branch and the exit of a loop whose test compares     ***)
(*** pointers or offsets with the same base, as ENSURES_WHILE_UP_TAC     ***)
(*** leaves them; LOOP_EXIT_TAC n simulates the n instructions from the  ***)
(*** test to the return.                                                 ***)

let LOOP_BACK_TAC execth =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC execth (1--1) THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC execth (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let LOOP_EXIT_TAC execth n =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC execth (1--1) THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC execth (2--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));;

(* ------------------------------------------------------------------------- *)
(* 32-bit values that the compiled code computes in 64-bit registers. A      *)
(* 32-bit result stored with a W register and read back through an X        *)
(* register appears as word_zx (word_zx x), and the mask of the sign of a    *)
(* 32-bit value z, computed with SXTW and ASR #31 (as mld_ct_cmask_neg_i32   *)
(* does), as word_zx (word_ishr (word_sxfrom 31 (word_subword (word_zx z)   *)
(* (0,32))) 31), with types of the model. SIGN_MASK_32_CONV turns the latter *)
(* into word_ishr z 31, proving the equation for the types it finds.         *)
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

let SIGN_MASK_32_CONV =
  let pat = `word_zx (word_ishr (word_sxfrom 31
               (word_subword (word_zx (z:int32)) (0,32))) 31):int32`
  and z = `z:int32` and ishr = `word_ishr:int32->num->int32` in
  fun tm ->
    let i = term_match [] pat tm in
    if instantiate i pat <> tm then failwith "SIGN_MASK_32_CONV" else
    let zt = instantiate i z and zv = genvar `:int32` in
    let th = prove
     (mk_forall(zv,mk_eq(subst [zv,zt] tm,
                         mk_comb(mk_comb(ishr,zv),`31`))),
      BITBLAST_TAC) in
    SPEC zt th;;

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

