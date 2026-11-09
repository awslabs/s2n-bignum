(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mld_H44, mld_H65 and mld_H87, which absorb up to *)
(* three inputs into one SHAKE256 context: absorbing two messages one after  *)
(* the other (mld_keccak_absorb of common/mldsa_native_fips202.ml, from the  *)
(* position the first one leaves) is absorbing their concatenation.          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;

(* ------------------------------------------------------------------------- *)
(* The position after absorbing.                                             *)
(* ------------------------------------------------------------------------- *)

let MLD_KECCAK_ABSORB_SND = prove
 (`!r S pos inlen M.
        SND(mld_keccak_absorb r S pos inlen M) = (pos + inlen) MOD r`,
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

let MLD_KECCAK_POS_ADD = prove
 (`!r a b. (a MOD r + b) MOD r = (a + b) MOD r`,
  REPEAT GEN_TAC THEN CONV_TAC MOD_DOWN_CONV THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The states after the blocks of two streams agree if they agree at some    *)
(* points a and b and the next m blocks after them are the same.             *)
(* ------------------------------------------------------------------------- *)

let MLD_KECCAK_ABSORB_BLOCKS_SHIFT = prove
 (`!r U V X Y a b.
     mld_keccak_absorb_blocks r U X a = mld_keccak_absorb_blocks r V Y b
     ==> !m. (!j. j < m
                  ==> (X DIV 2 EXP (8 * r * (a + j))) MOD 2 EXP (8 * r) =
                      (Y DIV 2 EXP (8 * r * (b + j))) MOD 2 EXP (8 * r))
             ==> mld_keccak_absorb_blocks r U X (a + m) =
                 mld_keccak_absorb_blocks r V Y (b + m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; mld_keccak_absorb_blocks] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `j < m:num` THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  REWRITE_TAC[ARITH_RULE `m < SUC m`]);;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream A + 2^(8 * r * n) * Y: below block n those of A, *)
(* and those of the stream t + 2^(8 * p) * M with t < 2^(8 * p) <= 2^(8 * r) *)
(* from block 1 on those of 2^(8 * p) * M.                                   *)
(* ------------------------------------------------------------------------- *)

let STREAM_MOD_ADD_MULT = prove
 (`!a b c d. a < d ==> (a + d * b) MOD (d * c) = a + d * (b MOD c)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `b DIV c` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`b:num`; `c:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV) [th]) ASSUME_TAC) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_AC] THEN ARITH_TAC;
    MP_TAC(SPECL [`b:num`; `c:num`] MOD_LT_EQ) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    TRANS_TAC LTE_TRANS `d + d * b MOD c` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `d + d * x = d * (x + 1)`; LE_MULT_LCANCEL] THEN
    SIMPLE_ARITH_TAC]);;

let STREAM_BLOCK_LOW = prove
 (`!r A Y n k.
        k < n
        ==> ((A + 2 EXP (8 * r * n) * Y) DIV 2 EXP (8 * r * k)) MOD
            2 EXP (8 * r) =
            (A DIV 2 EXP (8 * r * k)) MOD 2 EXP (8 * r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * r * n) =
                2 EXP (8 * r * k) * 2 EXP (8 * r) * 2 EXP (8 * r * (n - k - 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    MP_TAC(ARITH_RULE `k < n ==> n = k + 1 + (n - k - 1)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let STREAM_BLOCK_HIGH = prove
 (`!r t p M j.
        t < 2 EXP (8 * p) /\ p <= r /\ 1 <= j
        ==> (t + 2 EXP (8 * p) * M) DIV 2 EXP (8 * r * j) =
            (2 EXP (8 * p) * M) DIV 2 EXP (8 * r * j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * r * j) = 2 EXP (8 * p) * 2 EXP (8 * r * j - 8 * p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> b = a + (b - a)`) THEN
    TRANS_TAC LE_TRANS `8 * r * 1` THEN CONJ_TAC THENL
     [SIMPLE_ARITH_TAC; REWRITE_TAC[LE_MULT_LCANCEL] THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN
  SIMP_TAC[DIV_MULT; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Absorbing M1 (l1 bytes) and then M2 (l2 bytes) from the position after M1 *)
(* is absorbing M1 + 2^(8 * l1) * M2. With n1 = (pos + l1) DIV r and p1 =    *)
(* (pos + l1) MOD r, the stream of the concatenation is that of M1 plus that *)
(* of M2 after its first n1 blocks: block n1 joins the last p1 bytes of the  *)
(* first stream with the first r - p1 bytes of the second one (a XOR of      *)
(* disjoint parts), and the later blocks are those of the second one.        *)
(* ------------------------------------------------------------------------- *)

let MLD_KECCAK_ABSORB_APPEND = prove
 (`!r S pos l1 l2 M1 M2.
        0 < r /\ M1 < 2 EXP (8 * l1)
        ==> mld_keccak_absorb r (FST(mld_keccak_absorb r S pos l1 M1))
                                (SND(mld_keccak_absorb r S pos l1 M1)) l2 M2 =
            mld_keccak_absorb r S pos (l1 + l2) (M1 + 2 EXP (8 * l1) * M2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[FST; SND] THEN
  MP_TAC(SPECL [`pos + l1`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ABBREV_TAC `n1 = (pos + l1) DIV r` THEN
  ABBREV_TAC `p1 = (pos + l1) MOD r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `pos + l1 + l2 = r * n1 + (p1 + l2)` SUBST1_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  ABBREV_TAC `n2 = (p1 + l2) DIV r` THEN

  (*** The stream as that of M1 and that of M2 after the first n1 blocks ***)

  SUBGOAL_THEN
   `2 EXP (8 * pos) * (M1 + 2 EXP (8 * l1) * M2) =
    2 EXP (8 * pos) * M1 + 2 EXP (8 * r * n1) * (2 EXP (8 * p1) * M2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (8 * pos) * M1 < 2 EXP (8 * r * n1) * 2 EXP (8 * p1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `8 * r * n1 + 8 * p1 = 8 * pos + 8 * l1` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[EXP_ADD; LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `st1 = 2 EXP (8 * pos) * M1` THEN
  ABBREV_TAC `st2 = 2 EXP (8 * p1) * M2` THEN

  (*** The first n1 blocks, and the rest of the stream after them ***)

  SUBGOAL_THEN
   `mld_keccak_absorb_blocks r S (st1 + 2 EXP (8 * r * n1) * st2) n1 =
    mld_keccak_absorb_blocks r S st1 n1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:num`; `S:1600 word`; `S:1600 word`;
                   `st1 + 2 EXP (8 * r * n1) * st2`; `st1:num`; `0`; `0`]
                  MLD_KECCAK_ABSORB_BLOCKS_SHIFT) THEN
    REWRITE_TAC[mld_keccak_absorb_blocks; ADD_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[STREAM_BLOCK_LOW];
    ALL_TAC] THEN
  SUBGOAL_THEN `st1 DIV 2 EXP (8 * r * n1) < 2 EXP (8 * p1)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = st1 DIV 2 EXP (8 * r * n1)` THEN
  SUBGOAL_THEN
   `!j. (st1 + 2 EXP (8 * r * n1) * st2) DIV 2 EXP (8 * r * (n1 + j)) =
        (t1 + st2) DIV 2 EXP (8 * r * j)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN

  (*** Block n1 joins the last bytes of M1 and the first bytes of M2 ***)

  SUBGOAL_THEN
   `word ((t1 + st2) MOD 2 EXP (8 * r)):1600 word =
    word (t1 MOD 2 EXP (8 * r)) ^^ word (st2 MOD 2 EXP (8 * r))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `2 EXP (8 * r) = 2 EXP (8 * p1) * 2 EXP (8 * (r - p1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "st2" THEN
    ASM_SIMP_TAC[STREAM_MOD_ADD_MULT; MOD_MULT2] THEN
    SUBGOAL_THEN `t1 MOD (2 EXP (8 * p1) * 2 EXP (8 * (r - p1))) = t1`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN
      TRANS_TAC LTE_TRANS `2 EXP (8 * p1)` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = a * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ; ARITH_RULE `1 <= n <=> ~(n = 0)`];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j
        ==> (t1 + st2) DIV 2 EXP (8 * r * j) = st2 DIV 2 EXP (8 * r * j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "st2" THEN
    MATCH_MP_TAC STREAM_BLOCK_HIGH THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN

  (*** No full block of the second part, or the blocks after n1 ***)

  STRUCT_CASES_TAC(SPEC `n2:num` num_CASES) THENL
   [REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1;
                mld_keccak_absorb_blocks] THEN
    ASM_REWRITE_TAC[WORD_XOR_ASSOC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `n1 + SUC n = (n1 + 1) + n /\ SUC n = 1 + n`] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL
   [`r:num`; `S:1600 word`;
    `mld_keccak_absorb_blocks r S st1 n1 ^^ word (t1 MOD 2 EXP (8 * r))`;
    `st1 + 2 EXP (8 * r * n1) * st2`; `st2:num`; `n1 + 1`; `1`]
   MLD_KECCAK_ABSORB_BLOCKS_SHIFT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM ADD1; ONE; mld_keccak_absorb_blocks] THEN
    REWRITE_TAC[GSYM ONE] THEN
    FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) && not(is_imp(snd(dest_forall(concl th)))))) THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; DIV_1] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[WORD_XOR_ASSOC];
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `(n1 + 1) + j = n1 + (1 + j)`] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same for SHAKE256 from the initial state, with the position after the *)
(* first part written as in the calls of mldsa_shake256_absorb by mld_H, the *)
(* bound for the concatenation of two inputs, and the concatenation of three *)
(* as two.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MLD_SHAKE256_ABSORB_APPEND = prove
 (`!l1 l2 M1 M2.
        M1 < 2 EXP (8 * l1)
        ==> mld_keccak_absorb 136
              (FST(mld_keccak_absorb 136 (word 0) 0 l1 M1)) (l1 MOD 136)
              l2 M2 =
            mld_keccak_absorb 136 (word 0) 0 (l1 + l2)
              (M1 + 2 EXP (8 * l1) * M2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`136`; `word 0:1600 word`; `0`; `l1:num`; `l2:num`;
                `M1:num`; `M2:num`] MLD_KECCAK_ABSORB_APPEND) THEN
  ASM_REWRITE_TAC[MLD_KECCAK_ABSORB_SND; ADD_CLAUSES; ARITH]);;

let BYTES_APPEND_BOUND = prove
 (`!l1 l2 M1 M2.
        M1 < 2 EXP (8 * l1) /\ M2 < 2 EXP (8 * l2)
        ==> M1 + 2 EXP (8 * l1) * M2 < 2 EXP (8 * (l1 + l2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * l1) + 2 EXP (8 * l1) * M2` THEN
  ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
  REWRITE_TAC[ARITH_RULE `a + a * b = a * (b + 1)`; LE_MULT_LCANCEL] THEN
  SIMPLE_ARITH_TAC);;

let BYTES_APPEND3 = prove
 (`!l1 l2 M1 M2 M3.
        (M1 + 2 EXP (8 * l1) * M2) + 2 EXP (8 * (l1 + l2)) * M3 =
        M1 + 2 EXP (8 * l1) * (M2 + 2 EXP (8 * l2) * M3)`,
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_ASSOC; ADD_ASSOC]);;

let MLD_SHAKE256_ABSORB_APPEND3 = prove
 (`!l1 l2 l3 M1 M2 M3.
        M1 < 2 EXP (8 * l1) /\ M2 < 2 EXP (8 * l2)
        ==> mld_keccak_absorb 136
             (FST(mld_keccak_absorb 136 (word 0) 0 (l1 + l2)
                   (M1 + 2 EXP (8 * l1) * M2)))
             ((l1 + l2) MOD 136) l3 M3 =
            mld_keccak_absorb 136 (word 0) 0 (l1 + l2 + l3)
             (M1 + 2 EXP (8 * l1) * (M2 + 2 EXP (8 * l2) * M3))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ADD_ASSOC; GSYM BYTES_APPEND3] THEN
  MATCH_MP_TAC MLD_SHAKE256_ABSORB_APPEND THEN
  MATCH_MP_TAC BYTES_APPEND_BOUND THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the proofs of mld_H. MLD_H_CASES_TAC splits on whether in2len *)
(* and in3len are zero, substitutes the zero lengths, and selects the branch *)
(* of the events template for each case. MLD_H_BOUND_TAC a adds the bound    *)
(* x < 2 EXP (8 * n) for the bytes x of length n read at a, and              *)
(* MLD_H_VAL_LEN_TAC k a l adds val(word l) = l for the length l of the      *)
(* buffer at a, which does not overlap the k bytes at stackpointer.          *)
(* MLD_H_GUARD_ADDR_TAC adds the fact about the GOT entry of the stack guard *)
(* in the form of the precondition of mldsa_shake256_finalize, for its call, *)
(* after the rewriting of word(pc + got_stack_chk_guard) to                  *)
(* word_add (word pc) (word got_stack_chk_guard) for the simulation.         *)
(* MLD_H_DISCHARGE_TAC is DISCHARGE_SAFETY_PROPERTY_TAC at the end of the    *)
(* part after a join whose events before it are a case of the template:      *)
(* memaccess_inbounds is split over each APPEND of the events, so that the   *)
(* events before the join, a conditional, are a conjunct of their own, to be *)
(* discharged by the assumption on them.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_H_CASES_TAC =
  ASM_CASES_TAC `in2len = 0` THEN ASM_CASES_TAC `in3len = 0` THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    concl th = `in2len = 0` || concl th = `in3len = 0`))) THEN
  W(fun (asl,w) ->
    REWRITE_TAC(mapfilter (fun (_,th) ->
      if concl th = `~(in2len = 0)` || concl th = `~(in3len = 0)`
      then EQF_INTRO th else fail()) asl));;

let MLD_H_READ_BYTES_BOUND = prove
 (`!a n (s:armstate) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let MLD_H_BOUND_TAC a =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,n)) s = x:num`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP MLD_H_READ_BYTES_BOUND th) else NO_TAC);;

let MLD_H_VAL_LEN_TAC k a l =
  SUBGOAL_THEN (subst [l,`l:num`] `val(word l:int64) = l`) ASSUME_TAC THENL
   [SUBGOAL_THEN
     (subst [k,`k:num`; l,`l:num`] `k + l <= 18446744073709551616`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
      MAP_EVERY EXISTS_TAC
       [`val(stackpointer:int64)`; mk_comb(`val:int64->num`,a)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let MLD_H_GUARD_ADDR_TAC =
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD] o check (fun th ->
    can (term_match []
          `read (memory :> bytes64 (word_add (word pc) (word n))) s =
           guard:int64`) (concl th)));;

let MLD_H_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;
