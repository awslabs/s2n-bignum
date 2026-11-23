(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The definitions and lemmas of mlkem-native's common/mlkem_specs.ml that   *)
(* its proofs of the x86 compress and decompress kernels need and that are   *)
(* not already in common/mlkem_mldsa.ml (which has the rest of that file).   *)
(* ========================================================================= *)

needs "common/mlkem_mldsa.ml";;

let compress_d4 = new_definition
  `compress_d4 (x:16 word) : 4 word =
   word((val x * 16 + 1664) DIV 3329)`;;

let compress_d5 = new_definition
  `compress_d5 (x:16 word) : 5 word =
   word((val x * 32 + 1664) DIV 3329)`;;

let compress_d10 = new_definition
  `compress_d10 (x:16 word) : 10 word =
   word((val x * 1024 + 1664) DIV 3329)`;;

let compress_d11 = new_definition
  `compress_d11 (x:16 word) : 11 word =
   word((val x * 2048 + 1664) DIV 3329)`;;

let decompress_d4 = new_definition
  `decompress_d4 (x:4 word) : 16 word =
   word((val x * 3329 + 8) DIV 16)`;;

let decompress_d5 = new_definition
  `decompress_d5 (x:5 word) : 16 word =
   word((val x * 3329 + 16) DIV 32)`;;

let decompress_d10 = new_definition
  `decompress_d10 (x:10 word) : 16 word =
   word((val x * 3329 + 512) DIV 1024)`;;

let decompress_d11 = new_definition
  `decompress_d11 (x:11 word) : 16 word =
   word((val x * 3329 + 1024) DIV 2048)`;;

let EL_SUB_LIST = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let PEEL_LEMMA = prove(
  `!P n. (!i. i < SUC n ==> P i) <=> (!i. i < n ==> P i) /\ P n`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    DISCH_TAC THEN CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
    STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let BRUTE_FORCE_WITH tac =
  let rec go (asl, w as gl) =
    let (i, body) = dest_forall w in
    let (ant, _) = dest_imp body in
    let n_tm = rand ant in
    let n = dest_small_numeral n_tm in
    if n = 0 then (GEN_TAC THEN SIMP_TAC[LT]) gl
    else
      let suc_eq = num_CONV n_tm in
      (CONV_TAC(BINDER_CONV(LAND_CONV(RAND_CONV(REWR_CONV suc_eq)))) THEN
       GEN_REWRITE_TAC I [PEEL_LEMMA] THEN
       CONJ_TAC THENL [ALL_TAC; 
         (fun gl2 -> try let r = tac gl2 in
           Printf.printf "Case %d proved\n%!" (n-1); r
          with e -> Printf.printf "Failed to prove case %d\n%!" (n-1); raise e)
       ] THEN
       go) gl
  in go;;

let COND_REWRITE_CONV solve thm : conv = fun tm ->
  let thm' = PART_MATCH (lhand o snd o dest_imp) thm tm in
  let precond = fst(dest_imp(concl thm')) in
  MP thm' (solve precond);;

let WORD_64_SUB_8_8_JOIN_16 = WORD_BLAST `!(x : 64 word).
         word_join (word_subword x (8,8) : 8 word) (word_subword x (0,8) : 8 word) =
         word_subword x (0,16) : 16 word`;;

let WORD_JOIN_AND_TYBIT0 = prove(
  `word_and (word_join (a:N word) (b:N word) : (N tybit0) word) (word_join (c:N word) (d:N word)) =
   word_join (word_and a c) (word_and b d)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (q <=> p /\ q)`) THEN ASM_ARITH_TAC);;

let WORD_JOIN_NOT_TYBIT0 = prove(
  `word_not (word_join (a:N word) (b:N word) : (N tybit0) word) =
   word_join (word_not a) (word_not b)`,
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_NOT; BIT_WORD_JOIN; DIMINDEX_TYBIT0] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i < 2 * dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> (~q <=> p /\ ~q)`) THEN ASM_ARITH_TAC);;

let WORD_SUBWORD_USHR_JOIN = prove(
  `word_subword (word_ushr (x:(N tybit0) word) (dimindex(:N))) (0,dimindex(:N)) : N word =
   word_subword x (dimindex(:N), dimindex(:N))`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR; DIMINDEX_TYBIT0] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES; ADD_SYM]);;

let WORD_SUBWORD_USHR_64 = REWRITE_RULE[DIMINDEX_CONV `dimindex(:64)`]
  (INST_TYPE [`:64`,`:N`] WORD_SUBWORD_USHR_JOIN);;

let WORD_SUBWORD_USHR_HIGH = prove(
  `word_subword (word_ushr (x:(N tybit0) word) (dimindex(:N))) (dimindex(:N),dimindex(:N)) : N word = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  SIMP_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR; BIT_WORD_0; DIMINDEX_TYBIT0] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (INST_TYPE [`:N tybit0`,`:N`] BIT_TRIVIAL)) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN ASM_ARITH_TAC);;

let WORD_MUL_SHL = prove(`!x y n. word_mul (word_shl y n) x = word_shl (word_mul x y) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD_SHL; EXP_2] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[MULT_AC]);;

let VAL_WORD_MUL_EXACT = prove(
  `!x y. val x * val y < 2 EXP dimindex(:N)
         ==> val(word_mul x y : N word) = val x * val y`,
  REWRITE_TAC[VAL_WORD_MUL] THEN SIMP_TAC[MOD_LT]);;

let VAL_WORD_ZX_EXACT = prove(
  `!(x:M word). val x < 2 EXP dimindex(:N) ==> val(word_zx x : N word) = val x`,
  REWRITE_TAC[VAL_WORD_ZX_GEN] THEN SIMP_TAC[MOD_LT]);;

let WORD_ZX_128_256_128 = prove(
  `!(x : 128 word). word_zx (word_zx x : 256 word) = x`,
  GEN_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `val (x:128 word) < 2 EXP 256` ASSUME_TAC THENL
  [MP_TAC(ISPEC `x:128 word` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_128] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
   ASM_SIMP_TAC[MOD_LT; WORD_VAL]]);;

let BYTES128_JOIN = prove(
  `!(b0:8 word) (b1:8 word) (b2:8 word) (b3:8 word)
    (b4:8 word) (b5:8 word) (b6:8 word) (b7:8 word)
    (b8:8 word) (b9:8 word) (b10:8 word) (b11:8 word)
    (b12:8 word) (b13:8 word) (b14:8 word) (b15:8 word).
    (word_zx:256 word->128 word)
    ((word_zx:128 word->256 word)
   (word(val b0 * 2 EXP (8 * 0) +
          val b1 * 2 EXP (8 * 1) +
          val b2 * 2 EXP (8 * 2) +
          val b3 * 2 EXP (8 * 3) +
          val b4 * 2 EXP (8 * 4) +
          val b5 * 2 EXP (8 * 5) +
          val b6 * 2 EXP (8 * 6) +
          val b7 * 2 EXP (8 * 7) +
          val b8 * 2 EXP (8 * 8) +
          val b9 * 2 EXP (8 * 9) +
          val b10 * 2 EXP (8 * 10) +
          val b11 * 2 EXP (8 * 11) +
          val b12 * 2 EXP (8 * 12) +
          val b13 * 2 EXP (8 * 13) +
          val b14 * 2 EXP (8 * 14) +
          val b15 * 2 EXP (8 * 15)) :128 word)) =
    word_join
      (word_join (word_join b15 b14 :16 word) (word_join b13 b12 :16 word) :32 word)
      (word_join
        (word_join (word_join b11 b10 :16 word) (word_join b9 b8 :16 word) :32 word)
        (word_join
          (word_join (word_join b7 b6 :16 word) (word_join b5 b4 :16 word) :32 word)
          (word_join (word_join b3 b2 :16 word) (word_join b1 b0 :16 word) :32 word)
          :64 word) :96 word) :128 word`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WORD_ZX_128_256_128; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `val (b0 : 8 word) * 2 EXP (8 * 0) +
                val (b1 : 8 word) * 2 EXP (8 * 1) +
                val (b2 : 8 word) * 2 EXP (8 * 2) +
                val (b3 : 8 word) * 2 EXP (8 * 3) +
                val (b4 : 8 word) * 2 EXP (8 * 4) +
                val (b5 : 8 word) * 2 EXP (8 * 5) +
                val (b6 : 8 word) * 2 EXP (8 * 6) +
                val (b7 : 8 word) * 2 EXP (8 * 7) +
                val (b8 : 8 word) * 2 EXP (8 * 8) +
                val (b9 : 8 word) * 2 EXP (8 * 9) +
                val (b10 : 8 word) * 2 EXP (8 * 10) +
                val (b11 : 8 word) * 2 EXP (8 * 11) +
                val (b12 : 8 word) * 2 EXP (8 * 12) +
                val (b13 : 8 word) * 2 EXP (8 * 13) +
                val (b14 : 8 word) * 2 EXP (8 * 14) +
                val (b15 : 8 word) * 2 EXP (8 * 15) = num_of_wordlist [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15]`
    SUBST1_TAC THENL [REWRITE_TAC [num_of_wordlist; LEFT_ADD_DISTRIB; GSYM EXP_ADD; DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC; ALL_TAC] THEN
    REPLICATE_TAC 4 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist] THEN
    REWRITE_TAC [num_of_wordlist] THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    BITBLAST_TAC);;

let BYTES256_JOIN = prove(
  `!(b0:8 word) (b1:8 word) (b2:8 word) (b3:8 word)
    (b4:8 word) (b5:8 word) (b6:8 word) (b7:8 word)
    (b8:8 word) (b9:8 word) (b10:8 word) (b11:8 word)
    (b12:8 word) (b13:8 word) (b14:8 word) (b15:8 word)
    (b16:8 word) (b17:8 word) (b18:8 word) (b19:8 word)
    (b20:8 word) (b21:8 word) (b22:8 word) (b23:8 word)
    (b24:8 word) (b25:8 word) (b26:8 word) (b27:8 word)
    (b28:8 word) (b29:8 word) (b30:8 word) (b31:8 word).
    word(val b0 * 2 EXP (8 * 0) +
         val b1 * 2 EXP (8 * 1) +
         val b2 * 2 EXP (8 * 2) +
         val b3 * 2 EXP (8 * 3) +
         val b4 * 2 EXP (8 * 4) +
         val b5 * 2 EXP (8 * 5) +
         val b6 * 2 EXP (8 * 6) +
         val b7 * 2 EXP (8 * 7) +
         val b8 * 2 EXP (8 * 8) +
         val b9 * 2 EXP (8 * 9) +
         val b10 * 2 EXP (8 * 10) +
         val b11 * 2 EXP (8 * 11) +
         val b12 * 2 EXP (8 * 12) +
         val b13 * 2 EXP (8 * 13) +
         val b14 * 2 EXP (8 * 14) +
         val b15 * 2 EXP (8 * 15) +
         val b16 * 2 EXP (8 * 16) +
         val b17 * 2 EXP (8 * 17) +
         val b18 * 2 EXP (8 * 18) +
         val b19 * 2 EXP (8 * 19) +
         val b20 * 2 EXP (8 * 20) +
         val b21 * 2 EXP (8 * 21) +
         val b22 * 2 EXP (8 * 22) +
         val b23 * 2 EXP (8 * 23) +
         val b24 * 2 EXP (8 * 24) +
         val b25 * 2 EXP (8 * 25) +
         val b26 * 2 EXP (8 * 26) +
         val b27 * 2 EXP (8 * 27) +
         val b28 * 2 EXP (8 * 28) +
         val b29 * 2 EXP (8 * 29) +
         val b30 * 2 EXP (8 * 30) +
         val b31 * 2 EXP (8 * 31)) :256 word =
    word_join
      (word_join
        (word_join (word_join b31 b30 :16 word) (word_join b29 b28 :16 word) :32 word)
        (word_join (word_join b27 b26 :16 word) (word_join b25 b24 :16 word) :32 word)
        :64 word)
      (word_join
        (word_join
          (word_join (word_join b23 b22 :16 word) (word_join b21 b20 :16 word) :32 word)
          (word_join (word_join b19 b18 :16 word) (word_join b17 b16 :16 word) :32 word)
          :64 word)
        (word_join
          (word_join
            (word_join (word_join b15 b14 :16 word) (word_join b13 b12 :16 word) :32 word)
            (word_join (word_join b11 b10 :16 word) (word_join b9 b8 :16 word) :32 word)
            :64 word)
          (word_join
            (word_join (word_join b7 b6 :16 word) (word_join b5 b4 :16 word) :32 word)
            (word_join (word_join b3 b2 :16 word) (word_join b1 b0 :16 word) :32 word)
            :64 word)
          :128 word)
        :192 word)
      :256 word`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `val (b0 : 8 word) * 2 EXP (8 * 0) +
                val (b1 : 8 word) * 2 EXP (8 * 1) +
                val (b2 : 8 word) * 2 EXP (8 * 2) +
                val (b3 : 8 word) * 2 EXP (8 * 3) +
                val (b4 : 8 word) * 2 EXP (8 * 4) +
                val (b5 : 8 word) * 2 EXP (8 * 5) +
                val (b6 : 8 word) * 2 EXP (8 * 6) +
                val (b7 : 8 word) * 2 EXP (8 * 7) +
                val (b8 : 8 word) * 2 EXP (8 * 8) +
                val (b9 : 8 word) * 2 EXP (8 * 9) +
                val (b10 : 8 word) * 2 EXP (8 * 10) +
                val (b11 : 8 word) * 2 EXP (8 * 11) +
                val (b12 : 8 word) * 2 EXP (8 * 12) +
                val (b13 : 8 word) * 2 EXP (8 * 13) +
                val (b14 : 8 word) * 2 EXP (8 * 14) +
                val (b15 : 8 word) * 2 EXP (8 * 15) +
                val (b16 : 8 word) * 2 EXP (8 * 16) +
                val (b17 : 8 word) * 2 EXP (8 * 17) +
                val (b18 : 8 word) * 2 EXP (8 * 18) +
                val (b19 : 8 word) * 2 EXP (8 * 19) +
                val (b20 : 8 word) * 2 EXP (8 * 20) +
                val (b21 : 8 word) * 2 EXP (8 * 21) +
                val (b22 : 8 word) * 2 EXP (8 * 22) +
                val (b23 : 8 word) * 2 EXP (8 * 23) +
                val (b24 : 8 word) * 2 EXP (8 * 24) +
                val (b25 : 8 word) * 2 EXP (8 * 25) +
                val (b26 : 8 word) * 2 EXP (8 * 26) +
                val (b27 : 8 word) * 2 EXP (8 * 27) +
                val (b28 : 8 word) * 2 EXP (8 * 28) +
                val (b29 : 8 word) * 2 EXP (8 * 29) +
                val (b30 : 8 word) * 2 EXP (8 * 30) +
                val (b31 : 8 word) * 2 EXP (8 * 31) = num_of_wordlist [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31]`
    SUBST1_TAC THENL [REWRITE_TAC [num_of_wordlist; LEFT_ADD_DISTRIB; GSYM EXP_ADD; DIMINDEX_CONV `dimindex(:8)`] THEN ARITH_TAC; ALL_TAC] THEN
    REPLICATE_TAC 5 (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
                     [GSYM NUM_OF_PAIR_WORDLIST]) THEN
    REWRITE_TAC[pair_wordlist] THEN
    REWRITE_TAC [num_of_wordlist] THEN
    CONV_TAC (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    BITBLAST_TAC);;
