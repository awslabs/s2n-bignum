(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Overlap checks in compiled code. When gcc vectorizes a loop that reads    *)
(* one array and writes another, it may add a check that the two do not      *)
(* overlap, and fall back to a scalar loop if they do, e.g. at -O3 in        *)
(* mlkem_poly_decompress_d4 with r the output (512 bytes) and a the input    *)
(* (128 bytes):                                                              *)
(*                                                                           *)
(*      add  x4, x0, #0x200        x4 = r + 512                              *)
(*      add  x2, x1, #0x80         x2 = a + 128                              *)
(*      cmp  x1, x4                C = (r + 512 <= a)                        *)
(*      ccmp x0, x2, #0x2, cc      if a < r + 512 then C = (a + 128 <= r)    *)
(*      b.cc <scalar loop>                                                   *)
(*                                                                           *)
(* The scalar loop is taken when a < r + 512 and r < a + 128 as unsigned     *)
(* numbers. NONOVERLAPPING_ALIAS_CHECK shows that this cannot happen when    *)
(* the regions do not overlap (modulo 2^64), and ALIAS_BRANCH_TAC uses it to *)
(* decide the branch after it has been simulated.                            *)
(* ========================================================================= *)

let NONOVERLAPPING_ALIAS_CHECK = prove
 (`!(a:int64) (b:int64) m n.
        nonoverlapping (a,m) (b,n) /\ ~(m = 0) /\ ~(n = 0) /\
        m < 2 EXP 64 /\ n < 2 EXP 64
        ==> val(word_add b (word n)) <= val a \/
            val(word_add a (word m)) <= val b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[nonoverlapping; DIMINDEX_64; NONOVERLAPPING_MODULO_DIFFERENCE] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND) THEN MP_TAC(ISPEC `b:int64` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_64] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(val(a:int64) + m) MOD 2 EXP 64 =
    (if val a + m < 2 EXP 64 then val a + m else (val a + m) - 2 EXP 64) /\
    (val(b:int64) + n) MOD 2 EXP 64 =
    (if val b + n < 2 EXP 64 then val b + n else (val b + n) - 2 EXP 64)`
   (CONJUNCTS_THEN (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_CASES THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term is_cond) (concl th)))) THEN
  REPEAT COND_CASES_TAC THEN REPEAT DISCH_TAC THEN
  MAP_FIRST (fun z -> FIRST_ASSUM(MP_TAC o SPEC z) THEN
     REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`;
                 INTEGER_RULE `(x:int == x - n) (mod n)`;
                 INTEGER_RULE `(x:int == x + n) (mod n)`] THEN
     REWRITE_TAC(map INT_ARITH
      [`!x y n:int. --n < y - x <=> x < y + n`;
       `!x y m:int. y - x < m <=> y < x + m`;
       `!x y n N:int. --n < (y - x) + N <=> x < (y + N) + n`;
       `!x y m N:int. (y - x) + N < m <=> y + N < x + m`;
       `!x y n N:int. --n < (y - x) - N <=> x + N < y + n`;
       `!x y m N:int. (y - x) - N < m <=> y < (x + m) + N`]) THEN
     REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_LT] THEN ASM_ARITH_TAC)
   [`&(val(b:int64)) - &(val(a:int64)):int`;
    `(&(val(b:int64)) - &(val(a:int64))) + &(2 EXP 64):int`;
    `(&(val(b:int64)) - &(val(a:int64))) - &(2 EXP 64):int`]);;

(*** The carry flag after a comparison, as the simulation gives it ***)

let VAL_WORD_SUB_FLAG = prove
 (`!x y:N word. &(val x) - &(val y):int = &(val(word_sub x y)) <=>
                val y <= val x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB]; ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `&0:int <= z /\ x < y ==> ~(x - y = z)`) THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC);;

(*** Decide the branch of the check, given the two regions as (a,m) and
 *** (b,n) with nonoverlapping (a,m) (b,n) among the assumptions, once
 *** the conditional branch has been simulated, so that the PC is
 *** "if p then <scalar> else <vector>": show ~p and simplify the PC.
 ***)

let ALIAS_BRANCH_TAC a m b n =
  MP_TAC(SPECL [a; b; m; n] NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_THEN(fun dth ->
    RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG]) THEN
    FIRST_X_ASSUM(fun th ->
      let c = concl th in
      if can (term_match [] `read PC s = if p then x else y`) c then
        let p = rand(rator(rator(rand c))) in
        SUBGOAL_THEN (mk_neg p) (fun th' -> ASSUME_TAC(REWRITE_RULE[th'] th))
        THENL
         [MP_TAC dth THEN
          REWRITE_TAC[TAUT `~ ~p <=> p`;
                      TAUT `(if c then x else T) <=> (c ==> x)`] THEN
          ARITH_TAC;
          ALL_TAC]
      else failwith "ALIAS_BRANCH_TAC"));;
