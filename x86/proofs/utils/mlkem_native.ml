(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see x86/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit and 16-bit arithmetic in the registers.           *)
(* ------------------------------------------------------------------------- *)

(*** Zero extension then truncation, or the reverse ***)

let WORD_ZX_ZX_GEN = prove
 (`!x:M word.
        dimindex(:P) <= dimindex(:N)
        ==> (word_zx:N word->P word) ((word_zx:M word->N word) x) = word_zx x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** Reading the 8-bit or 16-bit part of a register ***)

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

let WORD_VAL_MOD_65536 = prove
 (`!x:N word. word (val x MOD 65536):int16 = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `65536 = 2 EXP 16`] THEN
  REWRITE_TAC[GSYM DIMINDEX_16; WORD_MOD_SIZE; word_zx]);;

(*** The 16-bit part of a register after writing it ***)

let WORD_ZX_JOIN_48_16 = prove
 (`!(h:48 word) (l:int16). word_zx(word_join h l:int64):int16 = l`,
  BITBLAST_TAC);;

(*** Simplify the results of such arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_WORD_SIMP_TAC =
  REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536; WORD_ADD; WORD_MUL;
              WORD_VAL] THEN
  SIMP_TAC[WORD_ZX_ZX_GEN; WORD_ZX_TRIVIAL; DIMINDEX_8; DIMINDEX_16;
           DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_ZX_JOIN_48_16];;

(*** Cancellation of a common base address ***)

let WORD_ADD_LCANCEL_EQ = prove
 (`!a x y:N word. word_add a x = word_add a y <=> x = y`,
  MESON_TAC[WORD_RULE `word_sub (word_add a x) a:N word = x`]);;

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

(*** The Barrett reduction as compiled for x86, multiplying the bottom 16
 *** bits of the quotient by -3329 = 62207 in a 16-bit register
 ***)

let BARRED_GCC12_O2 = prove
 (`!x:int16.
     word_add x
      (word_mul (word_zx (word_ishr (word_add (word_mul (word_sx x)
                                                         (word 20159))
                                             (word 33554432)) 26:int32))
                (word 62207)):int16 =
     barred x`,
  GEN_TAC THEN REWRITE_TAC[GSYM BARRED_SCALAR] THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[ISPECL [`word_mul (word_sx (x:int16)) (word 20159):int32`;
                      `word 33554432:int32`] WORD_ADD_SYM] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BITBLAST_TAC);;

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
 (`!a:int64 (l:int16 list) n j s:x86state.
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
 (`!x:int64 n s:x86state.
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
