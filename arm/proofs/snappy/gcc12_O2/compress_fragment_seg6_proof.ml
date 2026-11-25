(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* CompressFragment, the segment from loop3 (phase 6 of the model, one probe *)
(* x of the unrolled search of the first 16 positions): the probe at ip + x *)
(* (the preloaded word for x = 0, the shifted 64-bit load otherwise), the    *)
(* hash table entry read and replaced, and then                              *)
(*   - a match: the fast literal of the x + 1 bytes [ne, ip + x) (tag byte   *)
(*     and a 16-byte copy), to loop6 (phase 4), two model steps;            *)
(*   - no match, x < 15: to loop3 with x + 1, directly or through loop2     *)
(*     with the next 64-bit load (every fourth probe), one model step;       *)
(*   - no match, x = 15: through join1 to loop4 (phase 2 at ip + 16) or to  *)
(*     join4 (phase 5, emit_remainder), one or two model steps.             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_seg6_spec.ml";;

let CF_EXEC = SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_LOAD64_LOW32 = prove
 (`!(l:byte list) p.
        p + 8 <= LENGTH l
        ==> word_zx (word (snappy_load64 l p):int64):int32 =
            word (snappy_load32 l p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`l:byte list`; `p:num`; `0`] SNAPPY_LOAD64_SHIFT_LOW32) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; ADD_CLAUSES; LE_0]);;
let SNAPPY_WORD_LOAD32_EQ = prove
 (`!(l:byte list) p q.
     (word (snappy_load32 l p):int32 = word (snappy_load32 l q)) <=>
     snappy_load32 l p = snappy_load32 l q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; SNAPPY_VAL_WORD_LOAD32]);;
let SNAPPY_SXFROM_SUBWORD_SMALL = prove
 (`!x. x < 2 EXP 31
       ==> word_sxfrom 31 (word_subword (word x:int64) (0,32):int64):int64 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SXFROM; BIT_WORD_SUBWORD;
              DIMINDEX_64; DIMINDEX_32; ADD_CLAUSES] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BIT_WORD; DIMINDEX_64] THEN
  ASM_CASES_TAC `i < 31` THENL
   [ASM_SIMP_TAC[ARITH_RULE `i < 31 ==> MIN 31 i = i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `~(i < 31) ==> MIN 31 i = 31`] THEN
    SUBGOAL_THEN `x DIV 2 EXP 31 = 0 /\ x DIV 2 EXP i = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    CONJ_TAC THEN MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LTE_TRANS `2 EXP 31` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;
let SNAPPY_OUT_LIT16 = prove
 (`!(m:(S,int64->byte)component) op (out:byte list) b (l:byte list) a k s.
        read (m :> bytes(op,LENGTH out)) s = num_of_bytelist out /\
        read (m :> bytes8 (word_add op (word (LENGTH out)))) s = b /\
        read (m :> bytes64 (word_add op (word (LENGTH out + 1)))) s =
          word(snappy_load64 l a) /\
        read (m :> bytes64 (word_add op (word ((LENGTH out + 1) + 8)))) s =
          word(snappy_load64 l (a + 8)) /\
        k <= 16 /\ a + 16 <= LENGTH l
        ==> read (m :> bytes(op,LENGTH(APPEND out (CONS b (SUB_LIST(a,k) l))))) s =
            num_of_bytelist(APPEND out (CONS b (SUB_LIST(a,k) l)))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[APPEND; APPEND_ASSOC]
   `APPEND (out:byte list) (CONS b d) = APPEND (APPEND out [b]) d`] THEN
  MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN CONJ_TAC THENL
   [MATCH_MP_TAC SNAPPY_READ_BYTES_APPEND THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LENGTH; num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES; GSYM ONE] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `bytes8`)) (concl th))) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES8_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES;
                DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `read (m :> bytes(word_add (op:int64) (word (LENGTH(out:byte list) + 1)),16)) (s:S) =
                (num_of_bytelist (l:byte list) DIV 256 EXP a) MOD 2 EXP 128`
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 = 8 + 8`; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `bytes64`)) (concl th)))) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; BYTES64_WBYTES; GSYM VAL_EQ; VAL_READ_WBYTES;
                DIMINDEX_64; VAL_WORD; snappy_load64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST;
                 ARITH_RULE `a + 16 <= l ==> a + 8 <= l /\ (a + 8) + 8 <= l`] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SNAPPY_EXP_256; LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
    REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                            18446744073709551616 * 18446744073709551616`;
                MOD_MULT_MOD] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `l + SUC 0 = l + 1`] THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST;
               ARITH_RULE `k <= 16 /\ a + 16 <= l ==> MIN k (l - a) = k`] THEN
  ASM_SIMP_TAC[SNAPPY_NUM_OF_SUB_LIST;
               ARITH_RULE `k <= 16 /\ a + 16 <= l ==> a + k <= l`] THEN
  MP_TAC(ISPECL [`word_add (op:int64) (word (LENGTH(out:byte list) + 1))`; `16`;
                 `k:num`; `read (m:(S,int64->byte)component) (s:S)`] READ_BYTES_MOD) THEN
  ASM_SIMP_TAC[ARITH_RULE `k <= 16 ==> MIN 16 k = k`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SNAPPY_EXP_256; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;
let S6_WORD_TAC : tactic =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC (VAL_WORD_SUBWORD :: SNAPPY_VAL_THMS) THEN
  REWRITE_TAC (VAL_WORD_SUBWORD :: SNAPPY_VAL_THMS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  (fun (asl,w) -> let bs = snappy_load_bounds w in
     (MAP_EVERY ASSUME_TAC bs THEN
      CONV_TAC (SNAPPY_MOD_ELIM_CONV (bs @ map snd asl))) (asl,w)) THEN
  TRY SNAPPY_ARITH_TAC;;
(* Arithmetic about the probe index x <= 15 by cases on its 16 values, with  *)
(* the numeric facts that mention x.                                         *)
let S6_ARITH_TAC : tactic = fun (asl,w) ->
  let xv = `x:num` in
  let ths = filter (fun th -> is_num_fact(concl th) && free_in xv (concl th))
              (map snd asl) in
  let body = itlist (curry mk_imp) (map concl ths) w in
  let lem = TAC_PROOF(([],mk_forall(xv,mk_imp(`x < 16`,body))),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN ARITH_TAC) in
  let xlt = TAC_PROOF((asl,`x < 16`), SNAPPY_ARITH_TAC) in
  ACCEPT_TAC(rev_itlist (fun th l -> MP l th) ths (MP (SPEC xv lem) xlt)) (asl,w);;
let S6_CMP16 = prove
 (`!q. q <= 3 ==> ((4 * q + 18446744073709551604) MOD 18446744073709551616 = 0 <=> q = 3)`,
  REWRITE_TAC[ARITH_RULE `q <= 3 <=> q < 4`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(* The 32-bit probe value: the csel of the preloaded word (x = 0) and the    *)
(* low 32 bits of the shifted 64-bit load is the load at ip + x; rewritten   *)
(* in the facts of X10 and X4.                                               *)

let S6_PROBE_TAC : tactic = fun (asl,w) ->
  let f = snd(find (fun (_,th) ->
    try lhand(lhs(concl th)) = `X10` with Failure _ -> false) asl) in
  let cnd = rand(rand(concl f)) in
  let eq = mk_eq(cnd, `word(snappy_load32 inp (ip + x)):int32`) in
  (SUBGOAL_THEN eq ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [SUBGOAL_THEN `x = 0` SUBST_ALL_TAC THENL
       [POP_ASSUM MP_TAC THEN
        REWRITE_TAC[WORD_SUB_0; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                    DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `x MOD 18446744073709551616 MOD 4294967296 = x`
         SUBST1_TAC THENL
         [MATCH_MP_TAC(MESON[MOD_LT] `a < b /\ a < c ==> (a MOD b) MOD c = a`) THEN
          SNAPPY_ARITH_TAC;
          REWRITE_TAC[]];
        REWRITE_TAC[ADD_CLAUSES; SNAPPY_WORD_ZX_WORD_64_32]];
      MP_TAC(SPECL [`inp:byte list`; `ip + 4 * x DIV 4`; `x MOD 4`]
        SNAPPY_LOAD64_SHIFT_LOW32) THEN
      ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN SNAPPY_ARITH_TAC];
    SNAPPY_REWRITE_FACTS_TAC [`X10`; `X4`] [ASSUME eq]]) (asl,w);;

(* The tag byte of the fast literal, x << 2, as word(4 * x).                 *)

let S6_TAG_TAC : tactic = fun (asl,w) ->
  let f = snd(find (fun (_,th) -> try let c = lhand(lhs(concl th)) in
            fst(dest_const(rator(rand c))) = "bytes8" &&
            rand(rand c) = `word_add (op:int64) (word (LENGTH(out:byte list)))`
          with Failure _ -> false) asl) in
  let t = rand(concl f) in
  let eq = mk_eq(t, `word(4 * x):byte`) in
  (SUBGOAL_THEN eq ASSUME_TAC THENL [S6_WORD_TAC; ALL_TAC] THEN
   SNAPPY_REWRITE_FACTS_TAC [lhand(lhs(concl f))] [ASSUME eq]) (asl,w);;

let S6_MACH_TAC (ths:thm list) =
  REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
    snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
    snappy_out] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC ths THEN SNAPPY_CF1_MACH_TAC;;

(* ------------------------------------------------------------------------- *)
(* The segment.                                                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_SEG6 = prove
 (SNAPPY_CF1_SEG6_STMT,
  SNAPPY_CF1_SEG_START_TAC THEN
  SNAPPY_ABBREV_TAC `mcl = 27 + LENGTH(inp:byte list) + LENGTH inp DIV 6` THEN
  ARM_BSTEP_TAC CF_EXEC (1--5) THEN
  S6_PROBE_TAC THEN
  SNAPPY_REWRITE_FACTS_TAC [`X4`]
   [MATCH_MP SNAPPY_HASH1_WORD
     (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
    SNAPPY_VAL_WORD_LOAD32] THEN
  SNAPPY_ABBREV_TAC `h = snappy_hash1 ts (snappy_load32 inp (ip + x))` THEN
  SNAPPY_TABLE_SPLIT_TAC `h:num`
   (EXPAND_TAC "h" THEN MATCH_MP_TAC SNAPPY_HASH1_LT THEN SNAPPY_ARITH_TAC) THEN
  SUBGOAL_THEN `t1(h:num) + 4 <= LENGTH(inp:byte list) /\ t1 h < 65536`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN SNAPPY_TBOUND_TAC `h:num`; ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word (t1(h:num)):int16):int64 = word (t1 h)`
   ASSUME_TAC THENL
   [REWRITE_TAC[word_zx] THEN AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
    REWRITE_TAC[DIMINDEX_16] THEN SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `word_zx (word_zx (word (2 * h):int64):int32):int64 = word (2 * h)`
   ASSUME_TAC THENL
   [REWRITE_TAC[SNAPPY_WORD_ZX_WORD_64_32] THEN REWRITE_TAC[word_zx] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN
    SNAPPY_ARITH_TAC;
    ALL_TAC] THEN
  SNAPPY_LOAD_TAC [32,`t1(h:num):num`] THEN
  ARM_BSTEP_TAC ~rewrites:
   [ASSUME `word_zx (word (t1(h:num)):int16):int64 = word (t1 h)`;
    ASSUME `word_zx (word_zx (word (2 * h):int64):int32):int64 = word (2 * h)`]
   CF_EXEC (6--11) THEN
  ARM_PC_REWRITE_TAC [VAL_EQ_0; WORD_SUB_EQ_0; SNAPPY_WORD_LOAD32_EQ] THEN
  ARM_PC_CASES_TAC NO_TAC THENL
   [(* A match: the fast literal, to loop6 *)
    SNAPPY_LOAD_TAC [64,`ne:num`; 64,`ne + 8`] THEN
    SUBGOAL_THEN `LENGTH(out:byte list) + 17 <= mcl` ASSUME_TAC THENL
     [SNAPPY_ARITH_TAC; ALL_TAC] THEN
    ARM_BSTEP_TAC CF_EXEC (12--25) THEN
    SNAPPY_TABLE_JOIN_TAC `h:num` `ip + x` THEN
    BSTEP_FINAL_TAC THEN
    SNAPPY_CF1_CUT_TAC 2 THEN
    SUBGOAL_THEN `(ip + x) - ne = x + 1` SUBST1_TAC THENL
     [SNAPPY_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `snappy_emit_literal (SUB_LIST (ne,x + 1) inp) =
                  CONS (word(4 * x)) (SUB_LIST(ne,x + 1) inp)` SUBST1_TAC THENL
     [REWRITE_TAC[snappy_emit_literal; LENGTH_SUB_LIST] THEN
      SUBGOAL_THEN `MIN (x + 1) (LENGTH(inp:byte list) - ne) - 1 = x`
       SUBST1_TAC THENL [SNAPPY_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `x < 60` (fun th -> REWRITE_TAC[th]) THEN SNAPPY_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH(APPEND out (CONS (word(4 * x)) (SUB_LIST(ne,x + 1) inp))) =
                  LENGTH (out:byte list) + x + 2` ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST] THEN SNAPPY_ARITH_TAC;
      ALL_TAC] THEN
    S6_TAG_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(op,LENGTH out + x + 2)) s25 =
      num_of_bytelist(APPEND out (CONS (word(4 * x))
                                    (SUB_LIST(ne,x + 1) (inp:byte list))))`
     ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        try fst(dest_const(rator(lhs(concl th)))) = "LENGTH" with Failure _ -> false)) THEN
      MATCH_MP_TAC SNAPPY_OUT_LIT16 THEN ASM_REWRITE_TAC[] THEN SNAPPY_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `word_sxfrom 31 (word_subword (word x:int64) (0,32):int64):int64 =
                  word x` ASSUME_TAC THENL
     [MATCH_MP_TAC SNAPPY_SXFROM_SUBWORD_SMALL THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
    SNAPPY_REWRITE_FACTS_TAC [`X0`; `X1`]
     [ASSUME `word_sxfrom 31 (word_subword (word x:int64) (0,32):int64):int64 =
              word x`] THEN
    S6_MACH_TAC
     [ASSUME `LENGTH(APPEND out (CONS (word(4 * x)) (SUB_LIST(ne,x + 1) inp))) =
              LENGTH (out:byte list) + x + 2`] THEN
    REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    (fun (asl,w) -> CONV_TAC (SNAPPY_MOD_ELIM_CONV (map snd asl)) (asl,w)) THEN
    COND_CASES_TAC THEN SNAPPY_ARITH_TAC;

    (* No match: the next probe *)
    ARM_BSTEP_TAC CF_EXEC (12--15) THEN
    SNAPPY_PC_NUM_TAC [] THEN
    ARM_PC_CASES_TAC NO_TAC THENL
     [(* the next probe of the same 64-bit load *)
      SUBGOAL_THEN `(x + 1) DIV 4 = x DIV 4 /\ (x + 1) MOD 4 = x MOD 4 + 1 /\
                    ~(x = 15)` STRIP_ASSUME_TAC THENL
       [S6_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `word_ushr (word (snappy_load64 inp (ip + 4 * x DIV 4) DIV
                         2 EXP (8 * x MOD 4)):int64) 8 =
        word (snappy_load64 inp (ip + 4 * x DIV 4) DIV 2 EXP (8 * (x MOD 4 + 1)))`
       ASSUME_TAC THENL
       [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD; DIMINDEX_64] THEN
        MP_TAC(SPECL [`inp:byte list`; `ip + 4 * x DIV 4`] SNAPPY_LOAD64_BOUND) THEN
        ABBREV_TAC `L = snappy_load64 inp (ip + 4 * x DIV 4)` THEN DISCH_TAC THEN
        SUBGOAL_THEN `!k. L DIV 2 EXP k < 2 EXP 64`
         (fun th -> SIMP_TAC[MOD_LT; th]) THENL
         [GEN_TAC THEN TRANS_TAC LET_TRANS `L:num` THEN
          ASM_REWRITE_TAC[DIV_LE];
          ALL_TAC] THEN
        REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; LEFT_ADD_DISTRIB; MULT_CLAUSES];
        ALL_TAC] THEN
      SNAPPY_REWRITE_FACTS_TAC [`X5`]
       [ASSUME `word_ushr (word (snappy_load64 inp (ip + 4 * x DIV 4) DIV
                                 2 EXP (8 * x MOD 4)):int64) 8 =
                word (snappy_load64 inp (ip + 4 * x DIV 4) DIV
                      2 EXP (8 * (x MOD 4 + 1)))`] THEN
      SNAPPY_TABLE_JOIN_TAC `h:num` `ip + x` THEN
      BSTEP_FINAL_TAC THEN
      SNAPPY_CF1_CUT_TAC 1 THEN
      S6_MACH_TAC [ASSUME `(x + 1) DIV 4 = x DIV 4`;
                   ASSUME `(x + 1) MOD 4 = x MOD 4 + 1`];

      (* every fourth probe: the next 64-bit load *)
      SUBGOAL_THEN `x DIV 4 <= 3 /\ x MOD 4 <= 3` STRIP_ASSUME_TAC THENL
       [S6_ARITH_TAC; ALL_TAC] THEN
      SNAPPY_LOAD_TAC [64,`(ne + 5) + 4 * x DIV 4`] THEN
      ARM_BSTEP_TAC CF_EXEC (16--19) THEN
      SNAPPY_PC_NUM_TAC [] THEN
      ARM_PC_REWRITE_TAC [MATCH_MP S6_CMP16 (ASSUME `x DIV 4 <= 3`)] THEN
      ARM_PC_CASES_TAC NO_TAC THENL
       [(* x < 15: through loop2 to loop3 *)
        ARM_BSTEP_TAC CF_EXEC (20--21) THEN
        SUBGOAL_THEN `(x + 1) DIV 4 = x DIV 4 + 1 /\ (x + 1) MOD 4 = 0 /\
                      ~(x = 15)` STRIP_ASSUME_TAC THENL
         [S6_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `ip + 4 * (x DIV 4 + 1) = (ne + 5) + 4 * x DIV 4`
         ASSUME_TAC THENL [SNAPPY_ARITH_TAC; ALL_TAC] THEN
        SNAPPY_TABLE_JOIN_TAC `h:num` `ip + x` THEN
        BSTEP_FINAL_TAC THEN
        SNAPPY_CF1_CUT_TAC 1 THEN
        S6_MACH_TAC [ASSUME `(x + 1) DIV 4 = x DIV 4 + 1`;
                     ASSUME `(x + 1) MOD 4 = 0`;
                     ASSUME `ip + 4 * (x DIV 4 + 1) = (ne + 5) + 4 * x DIV 4`;
                     MULT_CLAUSES; EXP; DIV_1];

        (* x = 15: through join1 *)
        SUBGOAL_THEN `x = 15 /\ (ne + 5) + 4 * x DIV 4 = ip + 16`
         STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL [S6_ARITH_TAC; ALL_TAC] THEN SNAPPY_ARITH_TAC;
          ALL_TAC] THEN
        SNAPPY_REWRITE_FACTS_TAC [`X5`]
         [ASSUME `(ne + 5) + 4 * x DIV 4 = ip + 16`] THEN
        SUBGOAL_THEN `word_zx (word (snappy_load64 inp (ip + 16)):int64):int32 =
                      word(snappy_load32 inp (ip + 16))` ASSUME_TAC THENL
         [MATCH_MP_TAC SNAPPY_LOAD64_LOW32 THEN SNAPPY_ARITH_TAC; ALL_TAC] THEN
        ARM_BSTEP_TAC ~rewrites:
         [ASSUME `word_zx (word (snappy_load64 inp (ip + 16)):int64):int32 =
                  word(snappy_load32 inp (ip + 16))`] CF_EXEC (20--32) THEN
        SNAPPY_REWRITE_FACTS_TAC [`X0`]
         [MATCH_MP SNAPPY_HASH1_WORD_ALT
           (ASSUME `snappy_table_size (LENGTH(inp:byte list)) = ts`);
          SNAPPY_VAL_WORD_LOAD32] THEN
        SNAPPY_PC_NUM_TAC [VAL_WORD_SUB_CASES] THEN
        ARM_PC_CASES_TAC NO_TAC THENL
         [(* to loop4 *)
          SNAPPY_TABLE_JOIN_TAC `h:num` `ip + x` THEN
          BSTEP_FINAL_TAC THEN
          SNAPPY_CF1_CUT_TAC 1 THEN
          SNAPPY_CF1_MACH_TAC;
          (* to join4 *)
          ARM_BSTEP_TAC CF_EXEC (33--35) THEN
          SNAPPY_TABLE_JOIN_TAC `h:num` `ip + x` THEN
          BSTEP_FINAL_TAC THEN
          SNAPPY_CF1_CUT_TAC 2 THEN
          SNAPPY_CF1_MACH_TAC]]]]);;
