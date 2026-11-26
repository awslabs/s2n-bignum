(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs about the whole image of a build of mlkem-native's   *)
(* libmlkem.so (see arm/mlkem_native/README.md), loaded at an address pc     *)
(* that is a multiple of 4096, as the dynamic loader does, and not           *)
(* wrapping around the end of the address space. None of them depends on     *)
(* the build. The rules whose names end in _FOR take the definition of the   *)
(* code of the image, a byte list <image>, as their first argument, and      *)
(* the file for the image of each build, e.g.                                *)
(* arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml, applies them to its         *)
(* image.                                                                    *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Addresses in the image when it is at a multiple of 4096.                  *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_4096_WORD_AND = prove
 (`!x:int64. aligned 4096 x <=> word_and x (word 4095) = word 0`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:int64`; `12`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 4096 < 4096`; ARITH_RULE
    `x < 4096 ==> x < 2 EXP 64`]);;

(*** The page and the offset within it computed by ADRP and ADD or LDR ***)

let PAGE_ADD_ALIGNED = prove
 (`!x y:int64.
        word_and x (word 4095) = word 0
        ==> word_and (word_add x y) (word 0xFFFFFFFFFFFFF000) =
            word_add x (word_and y (word 0xFFFFFFFFFFFFF000)) /\
            word_subword (word_add x y) (0,12):(12)word =
            word_subword y (0,12) /\
            word_subword (word_add x y) (4,8):(12)word =
            word_subword y (4,8)`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Vectors of polynomials. As in common/fips203/fips203.ml, a vector of k    *)
(* polynomials is given by its 256 * k coefficients, those of polynomial j   *)
(* being \i. x(256 * j + i). POLYVEC_SPLIT_TAC k splits an assumption        *)
(* !i. i < 256 * k ==> P i into one for each polynomial, POLYVEC_JOIN_TAC k  *)
(* reduces such a goal to the cases for the polynomials, and                 *)
(* POLYVEC_CASES_TAC reduces a goal !j. j < k ==> Q j to Q 0, ...,           *)
(* Q (k - 1), with the indices and offsets evaluated in each case.           *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_SPLIT = prove
 (`!k j P. (!i. i < 256 * k ==> P i) /\ j < k
           ==> !i. i < 256 ==> P(256 * j + i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  TRANS_TAC LTE_TRANS `256 * (j + 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let POLYVEC_JOIN = prove
 (`!k P. (!j. j < k ==> !i. i < 256 ==> P(256 * j + i))
         ==> !i. i < 256 * k ==> P i`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i DIV 256`) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `i MOD 256`) THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ; DIVISION_SIMP]);;

let POLYVEC_INDEX_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[LEFT_ADD_DISTRIB; MULT_ASSOC] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[ADD_CLAUSES];;

let POLYVEC_SPLIT_TAC k =
  let kt = mk_small_numeral k in
  let sth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (SPEC kt POLYVEC_SPLIT) in
  let jths = map (fun j ->
    let jt = mk_small_numeral j in
    jt,EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt kt)))
    (0--(k-1)) in
  let n = mk_small_numeral(256 * k) in
  FIRST_X_ASSUM(fun th ->
    let i,bod = dest_forall(concl th) in
    if rand(lhand bod) <> n then failwith "POLYVEC_SPLIT_TAC" else
    MAP_EVERY (fun (jt,jth) ->
      ASSUME_TAC(CONV_RULE POLYVEC_INDEX_CONV
        (MATCH_MP (SPEC jt sth) (CONJ th jth)))) jths);;

let POLYVEC_CASES_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC POLYVEC_INDEX_CONV;;

let POLYVEC_JOIN_TAC k =
  let kt = mk_small_numeral k in
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                (SPEC kt POLYVEC_JOIN)) THEN
  POLYVEC_CASES_TAC;;

(*** Bit fields of numbers and of words made from them ***)

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

(*** Splitting off the first m values of a sum of n + m values ***)

let NSUM_LT_ADD = prove
 (`!f m n. nsum {i | i < m + n} f =
           nsum {i | i < m} f + nsum {i | i < n} (\i. f(m + i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NSUM_CLAUSES_NUMSEG_LT; ADD_ASSOC]);;

(*** Coefficients loaded with sign extension, when known to be small ***)

let WORD_SX_SMALL = prove
 (`!y:int16. val y < 32768 ==> (word_sx y:int32) = word_zx y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let MOD_32_64 = prove
 (`!x. x MOD 4294967296 MOD 18446744073709551616 = x MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`x:num`; `4294967296`] MOD_LT_EQ) THEN ARITH_TAC);;

let BYTES_BITBLAST_TAC (asl,w) =
  let bts = setify (find_terms (fun t ->
     type_of t = `:byte` &&
     can (term_match [] `word(x MOD 256):byte`) t) w) in
  let vs = map (fun _ -> genvar `:byte`) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;

let MLKEM_NATIVE_ADRP_TAC =
  let mask = `word 0xFFFFFFFFFFFFF000:int64`
  and aligned_pc = `aligned 4096 (word pc:int64)` in
  let is_page t =
    match t with
      Comb(Comb(Const("word_and",_),
                Comb(Const("word",_),
                     Comb(Comb(Const("+",_),Var("pc",_)),k))),m)
        -> m = mask && is_numeral k
    | _ -> false in
  W(fun (asl,w) ->
    let ath = snd(find (fun (_,th) -> concl th = aligned_pc) asl) in
    let pth = GEN_ALL(CONJUNCT1(SPEC_ALL(MATCH_MP PAGE_ADD_ALIGNED
                (REWRITE_RULE[ALIGNED_4096_WORD_AND] ath)))) in
    let conv t =
      if is_page t then
        (LAND_CONV(REWR_CONV WORD_ADD) THENC REWR_CONV pth THENC
         RAND_CONV WORD_REDUCE_CONV) t
      else failwith "MLKEM_NATIVE_ADRP_TAC" in
    let rule th =
      if can (find_term is_page) (concl th) then
        CONV_RULE(ONCE_DEPTH_CONV conv THENC
                  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
      else th in
    RULE_ASSUM_TAC rule);;
