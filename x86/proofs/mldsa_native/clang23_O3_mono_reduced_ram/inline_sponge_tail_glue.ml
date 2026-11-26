(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The XOR of the last r = mlen MOD 136 bytes of the message into the state  *)
(* of the SHAKE256 that clang 23 inlines into mldsa{44,65,87}_signature_     *)
(* pre_hash_shake256 and mldsa{44,65,87}_verify_pre_hash_shake256, as a      *)
(* lemma from the label join1 (the exit of the loop over the blocks) to the  *)
(* label join5, where the padding is added. Which of the loops loop4 (32     *)
(* bytes per iteration), loop5 (4 bytes) and loop2 (1 byte) it runs depends  *)
(* on r (loop3 is never run, as the data and the state do not overlap), and  *)
(* each loop is used as the lemma of inline_sponge_tail_loops.ml.            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_tail_loops.ml";;

let SPONGE_TAIL_EXEC fn = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range fn];;

let SPONGE_TAIL_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e mp r R (S1:1600 word) rsp0 pc.
   r < 136 /\\ aligned 16 rsp0 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,r) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_join1) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read (memory :> bytes(mp,r)) s = R /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = S1 /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_join5) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = word_xor S1 (word R) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events mp r rsp0 pc /\\
             memaccess_inbounds e2 [mp,r; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic and tactics for the glue.                                      *)
(* ------------------------------------------------------------------------- *)

let TG_RES ths =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = x`) (concl th) || can (term_match [] `read events s = x`) (concl th)
    then REWRITE_RULE ths th else th);;
let TG_VALR = prove(`!r. r < 136 ==> val(word r:int64) = r`, REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `r < 136` THEN ARITH_TAC);;
let TG_AND3 = prove(`!r. r < 136 ==> (word r:int64) && word 3 = word (r MOD 4)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;
let TG_NOV_MONO = prove(`!n a m m' b k. m' <= m /\ nonoverlapping_modulo n (a,m) (b,k) ==> nonoverlapping_modulo n (a,m') (b,k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC) THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
(* a fact about a prefix of the data region that does not overlap the state *)
let TG_NOV_FACT lenterm =
  SUBGOAL_THEN (mk_comb(mk_comb(mk_comb(`nonoverlapping_modulo:num->num#num->num#num->bool`,`2 EXP 64`),
                mk_pair(`val (mp:int64)`,lenterm)), `(val (word_add rsp0 (word 32):int64),200)`)) ASSUME_TAC THENL
   [MATCH_MP_TAC TG_NOV_MONO THEN EXISTS_TAC `r:num` THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`r < 136`] THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC] ;
    ALL_TAC];;
let TG_JA_K k = prove(parse_term(Printf.sprintf "!a. (~(val(word_sub (word a) (word (a + %d)):int64) < 18446744073709551612 \\/
            val(word_sub (word_sub (word a) (word (a + %d))) (word 18446744073709551612):int64) = 0))" k k),
    GEN_TAC THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "word_sub (word a) (word (a + %d)):int64 = word_neg (word %d)" k k)) SUBST1_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;
let TG_JA = prove(`!a r. a < r /\ r < a + 4
     ==> (~(val(word_sub (word a) (word r):int64) < 18446744073709551612 \/
            val(word_sub (word_sub (word a) (word r)) (word 18446744073709551612):int64) = 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASM_CASES_TAC `r = a + 1` THENL [ASM_REWRITE_TAC[TG_JA_K 1]; ALL_TAC] THEN
  ASM_CASES_TAC `r = a + 2` THENL [ASM_REWRITE_TAC[TG_JA_K 2]; ALL_TAC] THEN
  SUBGOAL_THEN `r = a + 3` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[TG_JA_K 3]]);;
let TG_MOD1 = prove(`!a. 2 EXP 64 <= a /\ a < 2 * 2 EXP 64 ==> a MOD 2 EXP 64 = a - 2 EXP 64`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a = (a - 2 EXP 64) + 1 * 2 EXP 64` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;
let TG_CONG1 = NUMBER_RULE `!x n. (x + n == x) (mod n)`;;
let TG_CONG2 = NUMBER_RULE `!x y. x = y ==> (x == y) (mod n)`;;
let TG_ALIAS = prove(`!m s r. m < 2 EXP 64 /\ s < 2 EXP 64 /\ r < 136 /\ nonoverlapping_modulo (2 EXP 64) (m,r) (s,200)
         ==> ~(s < (m + r) MOD 2 EXP 64 /\ m < (s + r) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `nonoverlapping_modulo n (a,b) (c,d)`) (concl th))) THEN
  REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `m + r < 2 EXP 64` THEN ASM_CASES_TAC `s + r < 2 EXP 64` THENL
   [(* no wraps *)
    SUBGOAL_THEN `s < m + r /\ m < s + r` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC];
    (* s + r wraps *)
    SUBGOAL_THEN `m < (s + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m + 2 EXP 64 - s`]) THEN
    SUBGOAL_THEN `(m + 0 == s + (m + 2 EXP 64 - s)) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `s + (m + 2 EXP 64 - s) = m + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; TG_CONG1; CONG_SYM] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[TG_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* m + r wraps *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s + 2 EXP 64 - m`; `0`]) THEN
    SUBGOAL_THEN `(m + (s + 2 EXP 64 - m) == s + 0) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `m + (s + 2 EXP 64 - m) = s + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; TG_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* both wrap *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64 /\ m < (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64 /\ (s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC]]);;

let TG_ALIAS_W = prove(`!(mp:int64) (st:int64) r. r < 136 /\ nonoverlapping_modulo (2 EXP 64) (val mp,r) (val st,200)
    ==> ~(val st < val (word_add mp (word r)) /\ val mp < val (word_add st (word r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `mp:int64` VAL_BOUND)) THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `st:int64` VAL_BOUND)) THEN
  MP_TAC(SPECL [`val (mp:int64)`; `val (st:int64)`; `r:num`] TG_ALIAS) THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;
let TG_SETB = prove(`!(x:56 word) (c:bool). word (val (word_join x (if c then word 1 else word 0:byte):64 word) MOD 256):byte = (if c then word 1 else word 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN CONV_TAC WORD_BLAST);;
let TG_COND_AND = prove(`!c1 c2. ~(c1 /\ c2) ==> val((if c1 then word 1 else word 0:byte) && (if c2 then word 1 else word 0)) = 0`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC [`c1:bool`; `c2:bool`] THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;
let TG_AND_FC = prove(`!r. r < 136 ==> word_zx((word_zx (word r:int64):int32) && word 252):int64 = word (4 * (r DIV 4))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;
let TG_AND_E0 = prove(`!r. r < 136 ==> word_zx((word_zx (word r:int64):int32) && word 224):int64 = word (32 * (r DIV 32))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;
let TG_PREFIX = prove(`!(mp:int64) n r R (s:x86state). read (memory :> bytes(mp,r)) s = R /\ n <= r
     ==> read (memory :> bytes(mp,n)) s = R MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th))) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN r n = n` SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;
let TG_SUBMOD = prove(`!r k. r < 136 /\ 0 < k ==> val(word_sub (word r) (word (k * (r DIV k))):int64) = r MOD k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k * (r DIV k) <= r /\ r - k * (r DIV k) = r MOD k` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`r:num`; `k:num`] DIVISION) THEN ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB2] THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  MP_TAC(SPECL [`r:num`; `k:num`] MOD_LT_EQ) THEN ASM_SIMP_TAC[ARITH_RULE `0 < k ==> ~(k = 0)`] THEN
  DISCH_TAC THEN MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `136` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MP_TAC(SPECL [`r:num`; `k:num`] MOD_LE) THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]);;
let TG_VALR2 = prove(`!n. n < 136 ==> val(word n:int64) = n`, REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `n < 136` THEN ARITH_TAC);;

let TG_VARS = [`mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`];;
let TG_CALL_TAC exec name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc exec name
   ilist TG_VARS n;;

(* The alias test of the code (two comparisons of addresses, SETB, TEST and  *)
(* JE) before the vector path: as the data (mp,r) and the state at rsp0 + 32 *)
(* do not overlap, it takes the vector path. TG_ALIAS_W has the fact about   *)
(* the addresses.                                                            *)

let TG_ALIAS_TAC =
  FIRST_ASSUM(fun nov ->
    if can (term_match [] `nonoverlapping_modulo (2 EXP 64) (val mp,r) (val (word_add rsp0 (word 32)),200)`) (concl nov)
    then
      let a = MP (SPECL [`mp:int64`; `word_add rsp0 (word 32):int64`; `r:num`] TG_ALIAS_W) (CONJ (ASSUME `r < 136`) nov) in
      let eq1 = prove(`word_add (word_add rsp0 (word r)) (word 32):int64 = word_add (word_add rsp0 (word 32)) (word r)`, CONV_TAC WORD_RULE) in
      let ca = MP (SPECL [`val (word_add (rsp0:int64) (word 32)) < val (word_add (mp:int64) (word r))`;
                          `val (mp:int64) < val (word_add (word_add (rsp0:int64) (word 32)) (word r))`] TG_COND_AND) a in
      TG_RES [MULT_CLAUSES; TG_SETB; eq1; ca]
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* From the exit of loop5 (with RAX = 4 * (r DIV 4)) to join5: if r is not a *)
(* multiple of 4, the last r MOD 4 bytes with loop2.                         *)
(* ------------------------------------------------------------------------- *)

let SPONGE_T5_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e mp r R (S1:1600 word) rsp0 pc.
   r < 136 /\\ 4 <= r /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,r) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop5_exit) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read RAX s = word (4 * (r DIV 4)) /\\
          read (memory :> bytes(mp,r)) s = R /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S1 (word (R MOD 2 EXP (8 * (4 * (r DIV 4))))) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_join5) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = word_xor S1 (word R) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events mp r rsp0 pc /\\
             memaccess_inbounds e2 [mp,r; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;

let SPONGE_T5_TAC fn l2 =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l2) "H_L2" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(mp:int64) (r:num) (rsp0:int64) (pc:num).
      if r MOD 4 = 0 then f_ev_c mp r rsp0 pc else f_ev_d mp r rsp0 pc
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `R < 2 EXP (8 * r)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,r)) s0 = R`) (concl th) then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  MP_TAC(MATCH_MP TG_VALR (ASSUME `r < 136`)) THEN DISCH_TAC THEN
  ASM_CASES_TAC `r MOD 4 = 0` THENL
   [(*** a multiple of 4: nothing more ***)
    X86_STEPS_TAC exec (1--2) THEN
    TG_RES [MATCH_MP TG_SUBMOD (CONJ (ASSUME `r < 136`) (ARITH_RULE `0 < 4`)); ASSUME `r MOD 4 = 0`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 * (r DIV 4) = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [MP_TAC(SPECL [`r:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `R MOD 2 EXP (8 * r) = R` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    (*** the last r MOD 4 bytes ***)
    X86_STEPS_TAC exec (1--2) THEN
    TG_RES [MATCH_MP TG_SUBMOD (CONJ (ASSUME `r < 136`) (ARITH_RULE `0 < 4`)); ASSUME `~(r MOD 4 = 0)`] THEN
    X86_STEPS_TAC exec (3--6) THEN
    SUBGOAL_THEN `(word r:int64) && word 3 = word (r MOD 4)` ASSUME_TAC THENL [ASM_SIMP_TAC[MATCH_MP TG_AND3 (ASSUME `r < 136`)]; ALL_TAC] THEN
    TG_RES [ASSUME `(word r:int64) && word 3 = word (r MOD 4)`; MATCH_MP TG_VALR (ASSUME `r < 136`)] THEN
    X86_STEPS_TAC exec (7--7) THEN
    MP_TAC(MATCH_MP TG_VALR2 (ARITH_RULE `r MOD 4 < 136`)) THEN DISCH_TAC THEN
    TG_RES [ASSUME `val (word (r MOD 4):int64) = r MOD 4`; ASSUME `~(r MOD 4 = 0)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(word r:int64) && word 3 = word (r MOD 4)`]) THEN
    X86_STEPS_TAC exec (8--9) THEN
    SUBGOAL_THEN `4 * (r DIV 4) + r MOD 4 = r /\ 0 < r MOD 4 /\ 4 * (r DIV 4) < r /\ r < 4 * (r DIV 4) + 4` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(r MOD 4 = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r <= 136` ASSUME_TAC THENL [UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(S1:1600 word) ^^ word (R MOD 2 EXP (8 * (4 * (r DIV 4)))) = S1 ^^ word (R MOD 2 EXP (8 * (4 * (r DIV 4))))` ASSUME_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    TG_CALL_TAC exec "H_L2" [`rsp0:int64`; `mp:int64`; `4 * (r DIV 4)`; `r MOD 4`; `S1:1600 word`; `R:num`; `pc:num`] 10 THEN
    X86_STEPS_TAC exec (11--13) THEN
    TG_RES [MP (SPECL [`4 * (r DIV 4)`; `r:num`] TG_JA) (CONJ (ASSUME `4 * (r DIV 4) < r`) (ASSUME `r < 4 * (r DIV 4) + 4`))] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R MOD 2 EXP (8 * r) = R` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];;

(* ------------------------------------------------------------------------- *)
(* From the exit of loop4 (with RAX = 32 * (r DIV 32)) to join5: the rest of *)
(* the bytes with loop5 (and what follows it) or, if there are fewer than 4  *)
(* of them, with loop2.                                                      *)
(* ------------------------------------------------------------------------- *)

let SPONGE_T4_STMT fn = parse_term(Printf.sprintf
 "exists f_events. forall e mp r R (S1:1600 word) rsp0 pc.
   r < 136 /\\ 32 <= r /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (mp,r) (word_add rsp0 (word 32),200) /\\
   nonoverlapping (word pc,libmldsa_size) (word_add rsp0 (word 32),200)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + %s_loop4_exit) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read RAX s = word (32 * (r DIV 32)) /\\
          read (memory :> bytes(mp,r)) s = R /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s =
            word_xor S1 (word (R MOD 2 EXP (8 * (32 * (r DIV 32))))) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %s_join5) /\\
          read RSP s = rsp0 /\\ read R12 s = mp /\\ read R13 s = word r /\\
          read (memory :> wbytes (word_add rsp0 (word 32))) s = word_xor S1 (word R) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events mp r rsp0 pc /\\
             memaccess_inbounds e2 [mp,r; word_add rsp0 (word 32),200]
                                   [word_add rsp0 (word 32),200]))
     (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(word_add rsp0 (word 32),200)])"
  fn fn);;

let TG_TEST1C = prove
 (`!r. r < 136 ==> (val((word (r MOD 256):byte) && word 28) = 0 <=> r MOD 32 < 4)`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SPONGE_T4_TAC fn l2 l5 t5 =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l2) "H_L2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l5) "H_L5" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 t5) "H_T5" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(mp:int64) (r:num) (rsp0:int64) (pc:num).
      if r MOD 32 = 0 then f_ev_e mp r rsp0 pc
      else if r MOD 32 < 4 then f_ev_f mp r rsp0 pc
      else f_ev_gh mp r rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `R < 2 EXP (8 * r)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,r)) s0 = R`) (concl th) then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  MP_TAC(MATCH_MP TG_VALR (ASSUME `r < 136`)) THEN DISCH_TAC THEN
  ASM_CASES_TAC `r MOD 32 = 0` THENL
   [(*** a multiple of 32 ***)
    X86_STEPS_TAC exec (1--2) THEN
    TG_RES [MATCH_MP TG_SUBMOD (CONJ (ASSUME `r < 136`) (ARITH_RULE `0 < 32`)); ASSUME `r MOD 32 = 0`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `32 * (r DIV 32) = r` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [MP_TAC(SPECL [`r:num`; `32`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `R MOD 2 EXP (8 * r) = R` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    X86_STEPS_TAC exec (1--2) THEN
    TG_RES [MATCH_MP TG_SUBMOD (CONJ (ASSUME `r < 136`) (ARITH_RULE `0 < 32`)); ASSUME `~(r MOD 32 = 0)`] THEN
    X86_STEPS_TAC exec (3--4) THEN
    ASM_CASES_TAC `r MOD 32 < 4` THENL
     [(*** 1 to 3 bytes: loop2 ***)
      TG_RES [MATCH_MP TG_TEST1C (ASSUME `r < 136`); ASSUME `r MOD 32 < 4`] THEN
      X86_STEPS_TAC exec (5--8) THEN
      SUBGOAL_THEN `r MOD 4 = r MOD 32` ASSUME_TAC THENL
       [MP_TAC(SPECL [`r:num`; `4`; `8`] MOD_MOD) THEN CONV_TAC NUM_REDUCE_CONV THEN
        SUBGOAL_THEN `r MOD 32 MOD 4 = r MOD 32` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `32 * (r DIV 32) + r MOD 32 = r /\ 0 < r MOD 32 /\ 32 * (r DIV 32) < r /\ r < 32 * (r DIV 32) + 4 /\ r <= 136` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(r MOD 32 = 0)`; `r MOD 32 < 4`; `r < 136`] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(word r:int64) && word 3 = word (r MOD 32)` ASSUME_TAC THENL [ASM_SIMP_TAC[MATCH_MP TG_AND3 (ASSUME `r < 136`)]; ALL_TAC] THEN
      TG_RES [ASSUME `(word r:int64) && word 3 = word (r MOD 32)`; MATCH_MP TG_VALR2 (ARITH_RULE `r MOD 32 < 136`); ASSUME `~(r MOD 32 = 0)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `(word r:int64) && word 3 = word (r MOD 32)`]) THEN
      X86_STEPS_TAC exec (9--10) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MOD_MOD_REFL]) THEN
      TG_CALL_TAC exec "H_L2" [`rsp0:int64`; `mp:int64`; `32 * (r DIV 32)`; `r MOD 32`; `S1:1600 word`; `R:num`; `pc:num`] 11 THEN
      X86_STEPS_TAC exec (12--14) THEN
      TG_RES [MP (SPECL [`32 * (r DIV 32)`; `r:num`] TG_JA) (CONJ (ASSUME `32 * (r DIV 32) < r`) (ASSUME `r < 32 * (r DIV 32) + 4`))] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `R MOD 2 EXP (8 * r) = R` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
      (*** 4 or more bytes: loop5, then what follows it ***)
      TG_RES [MATCH_MP TG_TEST1C (ASSUME `r < 136`); ASSUME `~(r MOD 32 < 4)`] THEN
      X86_STEPS_TAC exec (5--8) THEN
      SUBGOAL_THEN `4 <= r` ASSUME_TAC THENL [UNDISCH_TAC `32 <= r` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `8 * (r DIV 32) < r DIV 4 /\ 4 * (r DIV 4) <= r /\ 4 * (r DIV 4) <= 136 /\ 0 < r DIV 4` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(r MOD 32 < 4)`; `r < 136`] THEN ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; MATCH_MP TG_AND_FC (ASSUME `r < 136`)]) THEN
      TG_NOV_FACT `4 * (r DIV 4)` THEN
      SUBGOAL_THEN `read (memory :> bytes (mp,4 * (r DIV 4))) s8 = R MOD 2 EXP (8 * (4 * (r DIV 4)))` ASSUME_TAC THENL
       [MATCH_MP_TAC TG_PREFIX THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `word (4 * (8 * (r DIV 32))):int64 = word (32 * (r DIV 32))` ASSUME_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `MIN (8 * (4 * (r DIV 4))) (8 * (4 * (8 * (r DIV 32)))) = 8 * (32 * (r DIV 32))` ASSUME_TAC THENL
       [UNDISCH_TAC `8 * (r DIV 32) < r DIV 4` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(S1:1600 word) ^^ word ((R MOD 2 EXP (8 * (4 * (r DIV 4)))) MOD 2 EXP (8 * (4 * (8 * (r DIV 32))))) = S1 ^^ word (R MOD 2 EXP (8 * (32 * (r DIV 32))))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[MOD_MOD_EXP_MIN]; ALL_TAC] THEN
      TG_CALL_TAC exec "H_L5" [`rsp0:int64`; `mp:int64`; `8 * (r DIV 32)`; `r DIV 4`; `S1:1600 word`; `R MOD 2 EXP (8 * (4 * (r DIV 4)))`; `pc:num`] 9 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MOD_MOD_REFL]) THEN
      TG_CALL_TAC exec "H_T5" [`mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] 10 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC]];;

(* ------------------------------------------------------------------------- *)
(* The whole of it, from join1 to join5, by the cases of r.                  *)
(* ------------------------------------------------------------------------- *)

let SPONGE_TAIL_TAC fn l2 l4 l5 t4 t5 =
  let exec = SPONGE_TAIL_EXEC fn in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l2) "H_L2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l4) "H_L4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 l5) "H_L5" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 t4) "H_T4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 t5) "H_T5" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(mp:int64) (r:num) (rsp0:int64) (pc:num).
      if r = 0 then f_ev_a mp r rsp0 pc
      else if r < 4 then f_ev_b mp r rsp0 pc
      else if r < 32 then f_ev_cd mp r rsp0 pc
      else f_ev_ef mp r rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `R < 2 EXP (8 * r)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes (mp,r)) s0 = R`) (concl th) then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  MP_TAC(MATCH_MP TG_VALR (ASSUME `r < 136`)) THEN DISCH_TAC THEN
  ASM_CASES_TAC `r = 0` THENL
   [(*** nothing to absorb ***)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `R = 0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `read (memory :> bytes (mp,0)) s0 = R`) (concl th))) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN MESON_TAC[]; ALL_TAC] THEN
    X86_STEPS_TAC exec (1--2) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_XOR_0] THEN
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  TG_RES [ASSUME `val (word r:int64) = r`; ASSUME `~(r = 0)`] THEN
  X86_STEPS_TAC exec (1--4) THEN
  ASM_CASES_TAC `r < 4` THENL
   [(*** 1 to 3 bytes: loop2 ***)
    TG_RES [ASSUME `r < 4`] THEN X86_STEPS_TAC exec (5--9) THEN
    SUBGOAL_THEN `(word r:int64) && word 3 = word r` ASSUME_TAC THENL [ASM_SIMP_TAC[MATCH_MP TG_AND3 (ASSUME `r < 136`); MOD_LT]; ALL_TAC] THEN
    TG_RES [ASSUME `(word r:int64) && word 3 = word r`; ASSUME `val (word r:int64) = r`; ASSUME `~(r = 0)`] THEN
    X86_STEPS_TAC exec (10--11) THEN
    FIRST_X_ASSUM(fun th -> if concl th = `(word r:int64) && word 3 = word r` then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    TG_NOV_FACT `0 + r` THEN
    SUBGOAL_THEN `0 < r /\ 0 + r <= 136` STRIP_ASSUME_TAC THENL [UNDISCH_TAC `~(r = 0)` THEN UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `read (memory :> bytes (mp,0 + r)) s11 = R` ASSUME_TAC THENL [REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(S1:1600 word) ^^ word (R MOD 2 EXP (8 * 0)) = S1` ASSUME_TAC THENL [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0]; ALL_TAC] THEN
    TG_CALL_TAC exec "H_L2" [`rsp0:int64`; `mp:int64`; `0`; `r:num`; `S1:1600 word`; `R:num`; `pc:num`] 12 THEN
    SUBGOAL_THEN `r < 0 + 4` ASSUME_TAC THENL [REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X86_STEPS_TAC exec (13--15) THEN
    TG_RES [MP (SPECL [`0`; `r:num`] TG_JA) (CONJ (ASSUME `0 < r`) (ASSUME `r < 0 + 4`))] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `R MOD 2 EXP (8 * (0 + r)) = R` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC MOD_LT THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  (*** at least 4 bytes: the vector path, as the data and the state do not overlap ***)
  TG_RES [ASSUME `~(r < 4)`] THEN X86_STEPS_TAC exec (5--14) THEN TG_ALIAS_TAC THEN
  ASM_CASES_TAC `r < 32` THENL
   [TG_RES [ASSUME `r < 32`] THEN X86_STEPS_TAC exec (15--22) THEN
    SUBGOAL_THEN `4 <= r` ASSUME_TAC THENL [UNDISCH_TAC `~(r < 4)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `0 < r DIV 4 /\ 4 * (r DIV 4) <= r /\ 4 * (r DIV 4) <= 136 /\ r < 4 * (r DIV 4) + 4` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`4 <= r`; `r < 136`] THEN ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; MATCH_MP TG_AND_FC (ASSUME `r < 136`)]) THEN
    TG_NOV_FACT `4 * (r DIV 4)` THEN
    SUBGOAL_THEN `read (memory :> bytes (mp,4 * (r DIV 4))) s22 = R MOD 2 EXP (8 * (4 * (r DIV 4)))` ASSUME_TAC THENL
     [MATCH_MP_TAC TG_PREFIX THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(S1:1600 word) ^^ word ((R MOD 2 EXP (8 * (4 * (r DIV 4)))) MOD 2 EXP (8 * (4 * 0))) = S1` ASSUME_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0]; ALL_TAC] THEN
    SUBGOAL_THEN `word (4 * 0):int64 = word 0` ASSUME_TAC THENL [REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
    TG_CALL_TAC exec "H_L5" [`rsp0:int64`; `mp:int64`; `0`; `r DIV 4`; `S1:1600 word`; `R MOD 2 EXP (8 * (4 * (r DIV 4)))`; `pc:num`] 23 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MOD_MOD_REFL]) THEN
    TG_CALL_TAC exec "H_T5" [`mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] 24 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    (*** at least 32 bytes: loop4, then what follows it ***)
    TG_RES [ASSUME `~(r < 32)`] THEN X86_STEPS_TAC exec (15--20) THEN
    SUBGOAL_THEN `32 <= r` ASSUME_TAC THENL [UNDISCH_TAC `~(r < 32)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `0 < r DIV 32 /\ 32 * (r DIV 32) <= r /\ 32 * (r DIV 32) <= 136` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`32 <= r`; `r < 136`] THEN ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; MATCH_MP TG_AND_E0 (ASSUME `r < 136`)]) THEN
    TG_NOV_FACT `32 * (r DIV 32)` THEN
    SUBGOAL_THEN `read (memory :> bytes (mp,32 * (r DIV 32))) s20 = R MOD 2 EXP (8 * (32 * (r DIV 32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC TG_PREFIX THEN EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TG_CALL_TAC exec "H_L4" [`rsp0:int64`; `mp:int64`; `r DIV 32`; `S1:1600 word`; `R MOD 2 EXP (8 * (32 * (r DIV 32)))`; `pc:num`] 21 THEN
    SUBGOAL_THEN `R MOD 2 EXP (8 * (32 * (r DIV 32))) = R MOD 2 EXP (8 * (32 * (r DIV 32)))` ASSUME_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    TG_CALL_TAC exec "H_T4" [`mp:int64`; `r:num`; `R:num`; `S1:1600 word`; `rsp0:int64`; `pc:num`] 22 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC];;
