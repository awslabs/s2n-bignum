(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see arm/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit arithmetic in W registers.                        *)
(* ------------------------------------------------------------------------- *)

(*** Writing and then reading a W register ***)

let WORD_ZX_ZX_32_64 = prove
 (`!x:int32. word_zx(word_zx x:int64) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

(*** Simplify the results of 32-bit arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_W_SIMP_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_ADD; WORD_MUL; WORD_VAL];;

(*** Truncation to 16 bits as reduction of the signed value ***)

let WORD_ZX_32_16 = prove
 (`!w:int32. (word_zx w:int16) = iword(ival w)`,
  REWRITE_TAC[GSYM word_sx] THEN BITBLAST_TAC);;

(*** Eliminate ival(iword t) when t is in range, innermost terms first ***)

let IVAL_IWORD_ELIM_TAC =
  REPEAT(W(fun (asl,w) ->
     let t = hd(sort free_in
        (find_terms (can (term_match [] `ival(iword x)`)) w)) in
     let th = PART_MATCH (lhand o rand) IVAL_IWORD t in
     MP_TAC th THEN REWRITE_TAC[DIMINDEX_16; DIMINDEX_32] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ANTS_TAC THENL [BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The scalar Barrett reduction mlk_barrett_reduce, as compiled using a pair *)
(* of 32-bit multiply-adds, is exactly the "barred" function used for the    *)
(* vectorized code.                                                          *)
(* ------------------------------------------------------------------------- *)

let BARRED_QUOTIENT = prove
 (`!x:int. ((&2 * x * &20159) div &65536 + &1024) div &2048 =
           (&33554432 + x * &20159) div &67108864`,
  GEN_TAC THEN
  SUBGOAL_THEN `(&2 * x * &20159) div &65536 = (x * &20159) div &32768`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_ARITH `&65536:int = &2 * &32768`] THEN
    SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; GSYM INT_MUL_ASSOC] THEN
    SIMP_TAC[INT_DIV_MUL; INT_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&33554432 + x:int = x + &1024 * &32768`;
              INT_ARITH `&67108864:int = &32768 * &2048`] THEN
  SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; INT_DIV_MUL_ADD;
           INT_OF_NUM_EQ; ARITH_EQ]);;

let BARRED_SCALAR = prove
 (`!x:int16.
        word_zx(word_add (word_sx x)
                  (word_mul (word_ishr (word_add (word 33554432)
                                         (word_mul (word_sx x) (word 20159)))
                                       26)
                            (word 4294963967)):int32):int16 =
        barred x`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_32_16; WORD_ADD_IMODULAR; WORD_MUL_IMODULAR;
              imodular; word_sx; IVAL_WORD_ISHR] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN IVAL_IWORD_ELIM_TAC THEN
  REWRITE_TAC[barred; iword_saturate; word_INT_MIN; word_INT_MAX;
              DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  IVAL_IWORD_ELIM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[BARRED_QUOTIENT] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Adding 3329 to a negative result of "barred" gives the remainder.         *)
(* ------------------------------------------------------------------------- *)

let BARRED_CONDADD_REM = prove
 (`!x:int16.
        ival(word_add (barred x)
                      (word_and (word_ishr (barred x) 15) (word 3329))) =
        ival x rem &3329`,
  let lemma = prove
   (`(y == x) (mod &3329) /\
     --(&1664) <= y /\ y <= &1664
     ==> x rem &3329 = if y < &0 then y + &3329 else y`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
    SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE) in
  REWRITE_TAC[MATCH_MP lemma (CONGBOUND_RULE `barred x`)] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reading arrays given as lists, and building byte arrays incrementally.    *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES16_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int16 list) n j s:armstate.
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int16 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `16 * j = 8 * (2 * j)`;
              ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:armstate.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

let SUB_LIST_0_SNOC2 = prove
 (`!l:A list n.
        n + 2 <= LENGTH l
        ==> SUB_LIST(0,n + 2) l =
            APPEND (SUB_LIST(0,n) l) [EL n l; EL (n + 1) l]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUB_LIST_SPLIT] THEN
  REWRITE_TAC[SUB_LIST_1] THEN
  ASM_SIMP_TAC[ARITH_RULE `n + 2 <= l ==> n < l /\ n + 1 < l`] THEN
  REWRITE_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* The scalar Montgomery reduction mlk_montgomery_reduce, as compiled. This  *)
(* subtracts a multiple of 3329 rather than adding one as "montred" does,    *)
(* so the results can differ by 3329 and the overflow condition is slightly  *)
(* different, but it satisfies the analogous congruence and bounds.          *)
(* ------------------------------------------------------------------------- *)

let montred_scalar = define
 `montred_scalar (t:int32):int16 =
  word_zx(word_ishr
   (word_add t
     (word_mul (word_sxfrom 15 (word_subword (word_mul t (word 4294963969))
                                             (0,16):int32))
               (word 4294963967)))
   16)`;;

let SXFROM_15_SUBWORD = prove
 (`!w:int32. word_sxfrom 15 (word_subword w (0,16):int32) =
             word_sx(word_zx w:int16)`,
  BITBLAST_TAC);;

let MONTRED_SCALAR_LEMMA = prove
 (`!t:int32.
        &2 pow 16 * ival(montred_scalar t) =
        ival(word_add t
              (word_mul (word_sx(word_zx(word_mul t (word 4294963969)):int16))
                        (word 4294963967)))`,
  GEN_TAC THEN REWRITE_TAC[montred_scalar; SXFROM_15_SUBWORD] THEN
  CONV_TAC(LAND_CONV(LAND_CONV INT_REDUCE_CONV)) THEN
  MATCH_MP_TAC(BITBLAST_RULE
   `word_zx x:int16 = word 0
    ==> &65536 * ival(word_zx(word_ishr (x:int32) 16):int16) = ival x`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o rand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o
    lhand o rand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM DIVIDES_MOD; DIMINDEX_16] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b + 1 == 0) (mod d) ==> d divides (x + (x * a) * b)`) THEN
  REWRITE_TAC[CONG] THEN ARITH_TAC);;

let INT_DIV_65536_BOUNDS = prove
 (`(!x w. &65536 * x <= w ==> x <= w div &65536) /\
   (!x w. w <= &65536 * x ==> w div &65536 <= x)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`w:int`; `&65536:int`] INT_DIVISION) THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_MONTRED_SCALAR = prove
 (`!a a' l u.
      (ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u
      ==> --(&2038402305) <= l /\ u <= &2038398975
          ==> (ival(montred_scalar a) == &(inverse_mod 3329 65536) * a')
              (mod &3329) /\
              (l - &109081343) div &2 pow 16 <= ival(montred_scalar a) /\
              ival(montred_scalar a) <= (u + &109084672) div &2 pow 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `&65536:int`; `&3329:int`] (INTEGER_RULE
   `!d e n:int. (e * d == &1) (mod n)
                ==> !x y. ((x == d * y) (mod n) <=>
                           (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC(MESON[INT_DIV_65536_BOUNDS]
   `P /\ l <= &65536 * x /\ &65536 * x <= u
    ==> P /\ l div &65536 <= x /\ x <= u div &65536`) THEN
  REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV INT_POW_CONV)
               MONTRED_SCALAR_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_add c (word_mul a b) = iword(ival c + ival a * ival b)`] THEN
  ASM_SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  W(fun (asl,w) ->
    let t = find_term (fun t -> type_of t = `:int16` &&
                               can (term_match [] `word_zx x:int16`) t) w in
    MP_TAC(ISPEC t IVAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    find_term (can (term_match [] `ival(iword x:int32)`)) o snd) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_POW_CONV) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `!p x y a:int. (x + y * --p == a) (mod p) <=> (x == a) (mod p)`] THEN
  ASM_INT_ARITH_TAC);;
